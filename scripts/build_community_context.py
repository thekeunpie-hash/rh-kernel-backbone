#!/usr/bin/env python3
"""Build objective community context (data/community_context.json & data/COMMUNITY_BRIEF.md)
from leanprover-community/riemann-hypothesis GitHub API + Lean Zulip RH threads.

Uses pure Python stdlib so it runs cleanly in GitHub Actions without extra pip packages.
Zulip collection tries, in order:
  1. ZULIP_EMAIL + ZULIP_API_KEY env vars (authenticated REST API),
  2. Web-public spectator endpoint on leanprover.zulipchat.com (#general),
  3. Local rh_zulip_*.json cache file if present.
"""

import glob
import http.cookiejar
import json
import os
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO = "leanprover-community/riemann-hypothesis"
GH_API = f"https://api.github.com/repos/{REPO}"
ZULIP_SITE = "https://leanprover.zulipchat.com"
ZULIP_STREAM_ID = 113488  # general

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "data"
OUT_DIR.mkdir(exist_ok=True)

ASSOC_RANK = {
    "OWNER": 4,
    "MEMBER": 3,
    "COLLABORATOR": 2,
    "CONTRIBUTOR": 1,
    "FIRST_TIME_CONTRIBUTOR": 0,
    "NONE": 0,
}


def gh_get_json(url: str):
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "rh-kernel-backbone-context/1.0",
    }
    token = os.environ.get("GITHUB_TOKEN", "")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read().decode("utf-8"))


def gh_get_paginated(url: str, max_pages: int = 10):
    items = []
    for page in range(1, max_pages + 1):
        sep = "&" if "?" in url else "?"
        batch = gh_get_json(f"{url}{sep}per_page=100&page={page}")
        if not isinstance(batch, list) or not batch:
            break
        items.extend(batch)
        if len(batch) < 100:
            break
    return items


def collect_github():
    prs = gh_get_paginated(f"{GH_API}/pulls?state=all", max_pages=6)
    commits = gh_get_paginated(f"{GH_API}/commits", max_pages=3)

    people = defaultdict(lambda: {
        "association": "NONE",
        "prs_opened": [],
        "prs_merged": [],
        "prs_batch_queue": [],
        "main_commits": 0,
        "merge_commits_authored": 0,
    })

    for pr in prs:
        user = (pr.get("user") or {}).get("login")
        if not user or user.endswith("[bot]"):
            continue
        p = people[user]
        assoc = pr.get("author_association", "NONE")
        if ASSOC_RANK.get(assoc, 0) > ASSOC_RANK.get(p["association"], 0):
            p["association"] = assoc
        labels = [lb.get("name", "") for lb in pr.get("labels", [])]
        entry = {
            "number": pr["number"],
            "title": pr["title"],
            "state": pr["state"],
            "batch_queue": "batch queue" in labels,
        }
        p["prs_opened"].append(entry)
        if pr.get("merged_at"):
            p["prs_merged"].append(entry)
        elif pr["state"] == "open" and "batch queue" in labels:
            p["prs_batch_queue"].append(entry)

    for c in commits:
        author = (c.get("author") or {}).get("login")
        committer = (c.get("committer") or {}).get("login")
        msg = (c.get("commit") or {}).get("message", "")
        if author and not author.endswith("[bot]"):
            people[author]["main_commits"] += 1
        if committer and committer != "web-flow" and not committer.endswith("[bot]"):
            first_line = msg.splitlines()[0] if msg else ""
            if first_line.startswith("Merge pull request") or "Merge" in first_line:
                people[committer]["merge_commits_authored"] += 1

    for login, p in people.items():
        if p["association"] in ("OWNER", "MEMBER", "COLLABORATOR") or p["merge_commits_authored"] >= 2:
            p["tier"] = "maintainer_or_collaborator"
        elif len(p["prs_merged"]) >= 2 or p["main_commits"] >= 3 or len(p["prs_batch_queue"]) >= 3:
            p["tier"] = "active_contributor"
        else:
            p["tier"] = "contributor"

    return dict(people)


def fetch_zulip_spectator(max_pages: int = 4):
    """Fetch recent #general RH messages via Zulip web-public spectator mode (no API key needed)."""
    cj = http.cookiejar.CookieJar()
    op = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(cj))
    op.addheaders = [("User-Agent", "rh-kernel-backbone-context/1.0")]
    op.open(f"{ZULIP_SITE}/", timeout=20).read()
    csrf = next((c.value for c in cj if "csrf" in c.name), "")

    by_topic = defaultdict(list)
    seen = set()
    anchor = "newest"
    for _ in range(max_pages):
        params = urllib.parse.urlencode({
            "anchor": str(anchor),
            "num_before": "200",
            "num_after": "0",
            "apply_markdown": "false",
            "narrow": json.dumps([
                {"operator": "channels", "operand": "web-public"},
                {"operator": "channel", "operand": "general"},
            ]),
        })
        req = urllib.request.Request(
            f"{ZULIP_SITE}/json/messages?{params}",
            headers={"X-CSRFToken": csrf, "Referer": f"{ZULIP_SITE}/"},
        )
        with op.open(req, timeout=25) as r:
            d = json.loads(r.read().decode("utf-8"))
        msgs = d.get("messages", [])
        if not msgs:
            break
        for m in msgs:
            if m["id"] in seen:
                continue
            seen.add(m["id"])
            subj = m.get("subject", "")
            low = subj.lower()
            if low.startswith("rh:") or "alpöge" in low or "alpoge" in low or "riemann" in low:
                by_topic[subj].append(m)
        if d.get("found_oldest"):
            break
        anchor = min(m["id"] for m in msgs) - 1
        time.sleep(0.25)
    return dict(by_topic)


def load_or_fetch_zulip():
    # 1) Local cache if present in repo or parent downloads dir
    for pattern in [str(ROOT / "rh_zulip_*.json"), str(ROOT.parent / "rh_zulip_*.json")]:
        candidates = sorted(glob.glob(pattern))
        if candidates:
            try:
                return json.loads(Path(candidates[-1]).read_text(encoding="utf-8"))
            except Exception:
                pass
    # 2) Web-public spectator fetch (works in CI without secrets)
    try:
        return fetch_zulip_spectator(max_pages=4)
    except Exception as exc:
        print(f"Warning: Zulip spectator fetch skipped ({exc})")
        return {}


def summarize_zulip(zulip_data):
    stats = defaultdict(lambda: {"messages": 0, "reactions_received": 0, "topics": Counter()})
    recent_highlights = []

    for topic, msgs in zulip_data.items():
        for m in msgs:
            sender = m.get("sender_full_name")
            if not sender or sender == "Notification Bot":
                continue
            rx_count = len(m.get("reactions", []))
            stats[sender]["messages"] += 1
            stats[sender]["reactions_received"] += rx_count
            stats[sender]["topics"][topic] += 1
            if rx_count >= 2:
                recent_highlights.append({
                    "topic": topic,
                    "sender": sender,
                    "reactions": rx_count,
                    "snippet": m.get("content", "")[:240].replace("\n", " "),
                })

    recent_highlights.sort(key=lambda x: x["reactions"], reverse=True)
    return (
        {
            k: {
                "messages": v["messages"],
                "reactions_received": v["reactions_received"],
                "topics": dict(v["topics"]),
            }
            for k, v in stats.items()
        },
        recent_highlights[:40],
    )


def write_brief(gh_people, zulip_stats, highlights, id_map):
    now_iso = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    lines = [f"# Community Context Brief (Auto-generated {now_iso})\n"]

    lines.append("## 1. Maintainers & Collaborators (GitHub Ground Truth)")
    for login, p in sorted(gh_people.items(), key=lambda kv: (-kv[1]["main_commits"], -len(kv[1]["prs_merged"]), kv[0])):
        if p["tier"] == "maintainer_or_collaborator":
            pr_nums = ", ".join(f"#{x['number']}" for x in p["prs_merged"][:8]) or "none"
            zname = id_map.get(login, "")
            zstr = f" / {zname}" if zname else ""
            lines.append(
                f"- **{login}**{zstr} (`{p['association']}`): merged PRs={len(p['prs_merged'])} ({pr_nums}), main commits={p['main_commits']}"
            )

    lines.append("\n## 2. Active Contributors (GitHub)")
    for login, p in sorted(
        gh_people.items(),
        key=lambda kv: (-len(kv[1]["prs_merged"]), -len(kv[1]["prs_batch_queue"]), -len(kv[1]["prs_opened"]), kv[0]),
    ):
        if p["tier"] != "maintainer_or_collaborator" and (p["prs_merged"] or p["prs_batch_queue"]):
            merged = ", ".join(f"#{x['number']}" for x in p["prs_merged"][:5])
            queued = ", ".join(f"#{x['number']}" for x in p["prs_batch_queue"][:5])
            lines.append(
                f"- **{login}** (`{p['association']}`): merged={len(p['prs_merged'])} [{merged}], batch_queue={len(p['prs_batch_queue'])} [{queued}], opened={len(p['prs_opened'])}"
            )

    lines.append("\n## 3. Most Active Zulip Participants (RH Threads)")
    for name, s in sorted(zulip_stats.items(), key=lambda kv: (-kv[1]["reactions_received"], -kv[1]["messages"]))[:25]:
        lines.append(f"- **{name}**: {s['messages']} msgs, {s['reactions_received']} reactions")

    lines.append("\n## 4. High-Signal Zulip Messages (Community Vibe & Key Milestones)")
    for h in highlights[:25]:
        lines.append(f"- [{h['topic']}] **{h['sender']}** (rx:{h['reactions']}): {h['snippet']}")

    (OUT_DIR / "COMMUNITY_BRIEF.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main():
    id_map_path = OUT_DIR / "identity_map.json"
    id_map = {}
    if id_map_path.exists():
        id_map = json.loads(id_map_path.read_text(encoding="utf-8")).get("github_to_zulip", {})

    gh_people = collect_github()
    zulip_raw = load_or_fetch_zulip()
    zulip_stats, highlights = summarize_zulip(zulip_raw)

    (OUT_DIR / "community_context.json").write_text(
        json.dumps(
            {
                "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "github": gh_people,
                "zulip_stats": zulip_stats,
                "highlights": highlights,
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    write_brief(gh_people, zulip_stats, highlights, id_map)
    print(f"Generated {OUT_DIR / 'community_context.json'} and {OUT_DIR / 'COMMUNITY_BRIEF.md'} ({len(gh_people)} GH users, {len(zulip_stats)} Zulip users)")


if __name__ == "__main__":
    main()

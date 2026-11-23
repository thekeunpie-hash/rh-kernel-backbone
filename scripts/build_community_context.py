#!/usr/bin/env python3
"""Collect objective GitHub role/PR ground truth and Zulip RH thread context.

Produces `data/community_context.json` and `data/COMMUNITY_BRIEF.md` using only
the Python standard library so it works in GitHub Actions or locally with zero
external dependencies.
"""

from __future__ import annotations

import base64
import glob
import json
import os
import time
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from pathlib import Path

REPO = "leanprover-community/riemann-hypothesis"
GH_API = f"https://api.github.com/repos/{REPO}"
ZULIP_SITE = "https://leanprover.zulipchat.com"
ZULIP_STREAM_ID = 113488  # #general

ASSOC_RANK = {
    "OWNER": 4,
    "MEMBER": 3,
    "COLLABORATOR": 2,
    "CONTRIBUTOR": 1,
    "FIRST_TIME_CONTRIBUTOR": 0,
    "NONE": 0,
}


def http_get_json(url: str, headers: dict[str, str] | None = None, timeout: int = 30):
    req = urllib.request.Request(url, headers=headers or {})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def gh_get_paginated(url: str, max_pages: int = 10) -> list[dict]:
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "rh-kernel-backbone-context",
    }
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"

    items: list[dict] = []
    for page in range(1, max_pages + 1):
        sep = "&" if "?" in url else "?"
        batch = http_get_json(f"{url}{sep}per_page=100&page={page}", headers=headers)
        if not batch:
            break
        items.extend(batch)
        if len(batch) < 100:
            break
    return items


def collect_github() -> dict[str, dict]:
    prs = gh_get_paginated(f"{GH_API}/pulls?state=all", max_pages=10)
    commits = gh_get_paginated(f"{GH_API}/commits", max_pages=5)

    people: dict[str, dict] = defaultdict(lambda: {
        "association": "NONE",
        "prs_opened": [],
        "prs_merged": [],
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
        entry = {"number": pr["number"], "title": pr["title"], "state": pr["state"]}
        p["prs_opened"].append(entry)
        if pr.get("merged_at"):
            p["prs_merged"].append(entry)

    for c in commits:
        author = (c.get("author") or {}).get("login")
        committer = (c.get("committer") or {}).get("login")
        msg = (c.get("commit") or {}).get("message", "")
        if author and not author.endswith("[bot]"):
            people[author]["main_commits"] += 1
        if committer and committer != "web-flow" and not committer.endswith("[bot]"):
            if msg.startswith("Merge pull request") or "Merge" in msg.splitlines()[0]:
                people[committer]["merge_commits_authored"] += 1

    for p in people.values():
        if p["association"] in ("OWNER", "MEMBER", "COLLABORATOR") or p["merge_commits_authored"] >= 2:
            p["tier"] = "collaborator"
        elif len(p["prs_merged"]) >= 2 or p["main_commits"] >= 3:
            p["tier"] = "active_contributor"
        else:
            p["tier"] = "contributor"

    return dict(people)


def load_or_fetch_zulip(root: Path) -> dict[str, list[dict]]:
    email = os.environ.get("ZULIP_EMAIL")
    api_key = os.environ.get("ZULIP_API_KEY")
    if email and api_key:
        b64 = base64.b64encode(f"{email}:{api_key}".encode("utf-8")).decode("ascii")
        headers = {"Authorization": f"Basic {b64}", "User-Agent": "rh-kernel-backbone-context"}
        topics = http_get_json(f"{ZULIP_SITE}/api/v1/users/me/{ZULIP_STREAM_ID}/topics", headers=headers).get("topics", [])
        targets = [t["name"] for t in topics if t["name"].startswith("RH:") or "Alpöge" in t["name"]]
        out: dict[str, list[dict]] = {}
        for topic in targets:
            narrow = json.dumps([
                {"operator": "stream", "operand": "general"},
                {"operator": "topic", "operand": topic},
            ])
            qs = urllib.parse.urlencode({
                "anchor": "newest",
                "num_before": "500",
                "num_after": "0",
                "narrow": narrow,
                "apply_markdown": "false",
            })
            data = http_get_json(f"{ZULIP_SITE}/api/v1/messages?{qs}", headers=headers)
            out[topic] = data.get("messages", [])
            time.sleep(0.3)
        return out

    candidates = sorted(glob.glob(str(root / "rh_zulip_*.json")))
    if candidates:
        raw = json.loads(Path(candidates[-1]).read_text(encoding="utf-8"))
        return raw if isinstance(raw, dict) else {"general": raw}
    return {}


def summarize_zulip(zulip_data: dict[str, list[dict]]):
    stats = defaultdict(lambda: {"messages": 0, "reactions_received": 0, "topics": Counter()})
    highlights: list[dict] = []

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
                highlights.append({
                    "topic": topic,
                    "sender": sender,
                    "reactions": rx_count,
                    "snippet": m.get("content", "")[:240].replace("\n", " "),
                })

    highlights.sort(key=lambda x: x["reactions"], reverse=True)
    clean_stats = {
        k: {
            "messages": v["messages"],
            "reactions_received": v["reactions_received"],
            "topics": dict(v["topics"]),
        }
        for k, v in stats.items()
    }
    return clean_stats, highlights[:40]


def write_brief(out_dir: Path, gh_people: dict[str, dict], zulip_stats: dict, highlights: list[dict]) -> None:
    lines = ["# Community Context Brief (Auto-generated)\n"]

    lines.append("## 1. Repo Collaborators (GitHub Ground Truth)")
    for login, p in sorted(gh_people.items(), key=lambda kv: (-len(kv[1]["prs_merged"]), -kv[1]["main_commits"])):
        if p["tier"] == "collaborator":
            pr_nums = ", ".join(f"#{x['number']}" for x in p["prs_merged"][:8]) or "none"
            lines.append(f"- **{login}** (`{p['association']}`): merged PRs={len(p['prs_merged'])} ({pr_nums}), main commits={p['main_commits']}")

    lines.append("\n## 2. Contributors (GitHub)")
    for login, p in sorted(gh_people.items(), key=lambda kv: (-len(kv[1]["prs_merged"]), -len(kv[1]["prs_opened"]))):
        if p["tier"] != "collaborator" and (p["prs_merged"] or p["prs_opened"]):
            merged = ", ".join(f"#{x['number']}" for x in p["prs_merged"][:5])
            opened = ", ".join(f"#{x['number']}" for x in p["prs_opened"][:5])
            lines.append(f"- **{login}** (`{p['association']}`): merged={len(p['prs_merged'])} [{merged}], opened={len(p['prs_opened'])} [{opened}]")

    if zulip_stats:
        lines.append("\n## 3. Most Active Zulip Participants (RH Threads)")
        for name, s in sorted(zulip_stats.items(), key=lambda kv: (-kv[1]["reactions_received"], -kv[1]["messages"]))[:25]:
            lines.append(f"- **{name}**: {s['messages']} msgs, {s['reactions_received']} reactions")

    if highlights:
        lines.append("\n## 4. High-Signal Zulip Messages")
        for h in highlights[:25]:
            lines.append(f"- [{h['topic']}] **{h['sender']}** (rx:{h['reactions']}): {h['snippet']}")

    (out_dir / "COMMUNITY_BRIEF.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    out_dir = root / "data"
    out_dir.mkdir(exist_ok=True)

    gh_people = collect_github()
    zulip_raw = load_or_fetch_zulip(root)
    zulip_stats, highlights = summarize_zulip(zulip_raw)

    (out_dir / "community_context.json").write_text(
        json.dumps({"github": gh_people, "zulip_stats": zulip_stats, "highlights": highlights}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    write_brief(out_dir, gh_people, zulip_stats, highlights)
    print(f"Generated {out_dir / 'community_context.json'} and {out_dir / 'COMMUNITY_BRIEF.md'}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Watch every RH thread on Lean Zulip #general and write data/zulip_rh_threads.json.

A thread is watched when its topic names RH as a word ("RH: ...", "RH AI-proof: ...", "Visualization for RH");
"GRH" alone does not count. Topics are read through Zulip's web-public spectator view (no account, no API key):
one call lists the channel's topics with their newest message id, and only a topic whose newest id moved since the
last run is read again, so a run every 5 minutes costs one request when nothing new was said.

Pure Python stdlib (GitHub Actions runs it without pip). Writes only public Zulip facts: topic, link, counts,
dates, participants and short excerpts of public messages.
"""

import http.cookiejar
import json
import re
import sys
import time
import urllib.parse
import urllib.request
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path

ZULIP_SITE = "https://leanprover.zulipchat.com"
STREAM_ID = 113488
STREAM_SLUG = "113488-general"
RH_TOPIC = re.compile(r"(?<![A-Za-z])RH(?![A-Za-z])")
SNIPPET = 280
PAGE = 1000
MAX_PAGES = 6
UA = "rh-kernel-backbone-zulip-watch/1.0"
FORMAT = 2  # bump when the per-thread summary changes; every thread is re-read once

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "data" / "zulip_rh_threads.json"


def is_rh_topic(name: str) -> bool:
    return bool(RH_TOPIC.search(name or ""))


def topic_url(name: str) -> str:
    # Zulip's own hash encoding: percent-encode, encode "." too, then "%" becomes "."
    enc = urllib.parse.quote(name, safe="").replace(".", "%2E").replace("%", ".")
    return f"{ZULIP_SITE}/#narrow/channel/{STREAM_SLUG}/topic/{enc}"


def iso(ts: int) -> str:
    return datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def plain(text: str) -> str:
    """Zulip markdown -> readable text: drop quoted blocks and "X said:" reply headers, unwrap mentions and links."""
    text = re.sub(r"(?s)(`{3,}|~{3,})[ \t]*(?:quote|spoiler)\b.*?\1", " ", text or "")
    text = re.sub(r"@_?\*\*([^*|]+)(?:\|\d+)?\*\*\s*\[said\]\([^)]*\)\s*:?", "", text)
    text = re.sub(r"@_?\*\*([^*|]+)(?:\|\d+)?\*\*", r"@\1", text)
    text = re.sub(r"#\*\*([^*]+)\*\*", r"#\1", text)
    text = re.sub(r"!?\[([^\]]*)\]\((https?://[^)]+)\)", lambda m: m.group(1) or m.group(2), text)
    text = re.sub(r"(?m)^\s*>\s?", "", text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
    return text


def snippet(text: str) -> str:
    text = re.sub(r"\s+", " ", plain(text)).strip()
    return text if len(text) <= SNIPPET else text[: SNIPPET - 1].rstrip() + "…"


class Spectator:
    def __init__(self):
        self.jar = http.cookiejar.CookieJar()
        self.op = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(self.jar))
        self.op.addheaders = [("User-Agent", UA)]
        self.op.open(f"{ZULIP_SITE}/", timeout=20).read()
        self.csrf = next((c.value for c in self.jar if "csrf" in c.name), "")

    def get(self, path: str, params: dict | None = None):
        url = f"{ZULIP_SITE}{path}" + (f"?{urllib.parse.urlencode(params)}" if params else "")
        req = urllib.request.Request(url, headers={"X-CSRFToken": self.csrf, "Referer": f"{ZULIP_SITE}/"})
        with self.op.open(req, timeout=30) as r:
            data = json.loads(r.read().decode("utf-8"))
        if data.get("result") != "success":
            raise RuntimeError(f"{path}: {data.get('msg') or data.get('code')}")
        return data

    def topics(self):
        return self.get(f"/json/users/me/{STREAM_ID}/topics").get("topics", [])

    def messages(self, topic: str):
        out, seen, anchor = [], set(), "newest"
        narrow = json.dumps([
            {"operator": "channels", "operand": "web-public"},
            {"operator": "channel", "operand": STREAM_ID},
            {"operator": "topic", "operand": topic},
        ])
        for _ in range(MAX_PAGES):
            d = self.get("/json/messages", {
                "anchor": str(anchor), "num_before": str(PAGE), "num_after": "0",
                "apply_markdown": "false", "narrow": narrow,
            })
            batch = [m for m in d.get("messages", []) if m["id"] not in seen]
            for m in batch:
                seen.add(m["id"])
            out.extend(batch)
            if d.get("found_oldest") or not batch:
                break
            anchor = min(m["id"] for m in batch) - 1
            time.sleep(0.3)
        out.sort(key=lambda m: m["id"])
        return out


def summarize(topic: str, max_id: int, msgs: list, now: datetime) -> dict:
    people = Counter()
    recent = []
    day_ago = (now - timedelta(days=1)).timestamp()
    week_ago = (now - timedelta(days=7)).timestamp()
    for m in msgs:
        name = m.get("sender_full_name") or ""
        if not name or name == "Notification Bot":
            continue
        people[name] += 1
    reacted = sorted(
        (m for m in msgs if len(m.get("reactions", [])) >= 2),
        key=lambda m: (-len(m.get("reactions", [])), -m["id"]),
    )[:3]
    for m in msgs[-3:]:
        recent.append({
            "id": m["id"], "at": iso(m["timestamp"]), "sender": m.get("sender_full_name", ""),
            "excerpt": snippet(m.get("content", "")),
        })
    daily = Counter(iso(m["timestamp"])[:10] for m in msgs)
    return {
        "topic": topic,
        "rh_prefix": topic.startswith("RH:"),
        "url": topic_url(topic),
        "max_id": max_id,
        "messages": len(msgs),
        "messages_24h": sum(1 for m in msgs if m["timestamp"] >= day_ago),
        "messages_7d": sum(1 for m in msgs if m["timestamp"] >= week_ago),
        "first_at": iso(msgs[0]["timestamp"]) if msgs else None,
        "last_at": iso(msgs[-1]["timestamp"]) if msgs else None,
        "participants": [{"name": n, "messages": c} for n, c in people.most_common()],
        "daily_messages": dict(sorted(daily.items())),
        "latest": recent,
        "most_reacted": [{
            "id": m["id"], "at": iso(m["timestamp"]), "sender": m.get("sender_full_name", ""),
            "reactions": len(m.get("reactions", [])), "excerpt": snippet(m.get("content", "")),
        } for m in reacted],
    }


def main() -> int:
    now = datetime.now(timezone.utc)
    prev = {}
    if OUT.exists():
        try:
            old_payload = json.loads(OUT.read_text(encoding="utf-8"))
            if old_payload.get("format") == FORMAT:
                prev = {t["topic"]: t for t in old_payload.get("threads", [])}
        except Exception:
            prev = {}
    try:
        z = Spectator()
        listed = [t for t in z.topics() if is_rh_topic(t.get("name", ""))]
    except Exception as exc:
        print(f"Zulip RH watch skipped: {exc}")
        return 0
    threads, read = [], 0
    for t in listed:
        name, max_id = t["name"], int(t.get("max_id") or 0)
        old = prev.get(name)
        if old and old.get("max_id") == max_id:
            threads.append(old)
            continue
        try:
            threads.append(summarize(name, max_id, z.messages(name), now))
            read += 1
        except Exception as exc:
            print(f"Zulip topic {name!r} skipped: {exc}")
            if old:
                threads.append(old)
    threads.sort(key=lambda t: t.get("max_id", 0), reverse=True)
    changed = read > 0 or [t["topic"] for t in threads] != list(prev)
    if not changed and OUT.exists():
        print(f"Zulip RH watch: {len(threads)} threads, no new messages")
        return 0
    payload = {
        "format": FORMAT,
        "generated_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source": f"{ZULIP_SITE}/#narrow/channel/{STREAM_SLUG}",
        "rule": "topics in #general that name RH as a word",
        "threads": threads,
    }
    OUT.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Zulip RH watch: {len(threads)} threads, {read} re-read")
    return 0


if __name__ == "__main__":
    sys.exit(main())

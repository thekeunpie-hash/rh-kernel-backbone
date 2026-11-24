#!/usr/bin/env python3
"""Fetch the per-commit proof-size series published by https://rh-shrink.github.io/.

rh-shrink (unofficial, third party) measures every commit on
leanprover-community/riemann-hypothesis `main` with plain text search over the
`.lean` files (code lines without blanks/comments/imports, theorems, other
declarations, maxHeartbeats overrides, repeated statements) and publishes the
series as public JSON at /data.json, refreshed by its own GitHub Action every
15 minutes.

This script keeps a compact copy in data/rh_shrink.json: the original
(first measured) commit, the latest commit, how much of the original code is
left, the newest commits that changed code with their deltas, and a
(date, code) series for a sparkline. The file contains no fetch timestamp, so
it only changes (and the tracker only commits) when rh-shrink publishes a new
measurement. If a fetch fails, the previous file is kept.

Pure Python 3.11+ stdlib only. Run:
  python scripts/fetch_rh_shrink.py [--data data/rh_shrink.json]
"""

import argparse
import json
import urllib.error
import urllib.request
from pathlib import Path

DATA_URL = "https://rh-shrink.github.io/data.json"
SITE_URL = "https://rh-shrink.github.io/"
SOURCE_REPO = "https://github.com/rh-shrink/rh-shrink.github.io"
USER_AGENT = "rh-kernel-backbone-rh-shrink/1.0"
METRICS = ("files", "lines", "code", "theorems", "defs", "imports", "heartbeats", "repeats", "statements")
RECENT_CHANGES = 12
MAX_BYTES = 8 * 1024 * 1024


def get_json(url):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=45) as response:
        raw = response.read(MAX_BYTES + 1)
    if len(raw) > MAX_BYTES:
        raise ValueError(f"response larger than {MAX_BYTES} bytes")
    return json.loads(raw.decode("utf-8"))


def _int(value):
    return value if isinstance(value, int) and not isinstance(value, bool) else None


def _short_text(value, limit=160):
    if not isinstance(value, str):
        return None
    text = " ".join(value.split())
    return text if len(text) <= limit else text[: limit - 1] + "…"


def _point(commit):
    out = {
        "sha": commit.get("sha") if isinstance(commit.get("sha"), str) else None,
        "date": commit.get("date") if isinstance(commit.get("date"), str) else None,
        "subject": _short_text(commit.get("subject")),
        "pr": _int(commit.get("pr")),
    }
    for key in METRICS:
        out[key] = _int(commit.get(key))
    return out


def normalize(raw):
    commits = raw.get("commits") if isinstance(raw, dict) else None
    if not isinstance(commits, list):
        raise ValueError("data.json has no commits list")
    points = [_point(c) for c in commits if isinstance(c, dict)]
    points = [p for p in points if p["sha"] and p["date"] and p["code"] is not None]
    if not points:
        raise ValueError("data.json has no measurable commits")

    original, latest = points[0], points[-1]
    code_left_pct = None
    if original["code"]:
        code_left_pct = round(latest["code"] / original["code"] * 100, 2)

    changes = []
    for prev, cur in zip(points, points[1:]):
        delta = cur["code"] - prev["code"]
        if delta == 0:
            continue
        theorem_delta = None
        if cur["theorems"] is not None and prev["theorems"] is not None:
            theorem_delta = cur["theorems"] - prev["theorems"]
        changes.append({
            "sha": cur["sha"],
            "date": cur["date"],
            "subject": cur["subject"],
            "pr": cur["pr"],
            "code": cur["code"],
            "code_delta": delta,
            "theorems_delta": theorem_delta,
        })

    return {
        "source": {"site": SITE_URL, "data": DATA_URL, "repo": SOURCE_REPO,
                   "method": "text search over .lean files under src/, one point per main commit (rh-shrink collect.py)",
                   "schema_version": _int(raw.get("version"))},
        "commits_measured": len(points),
        "original": original,
        "latest": latest,
        "code_left_pct": code_left_pct,
        "code_removed": original["code"] - latest["code"],
        "recent_changes": list(reversed(changes[-RECENT_CHANGES:])),
        "series": [[p["date"], p["code"]] for p in points],
    }


def main():
    parser = argparse.ArgumentParser(description="Fetch the rh-shrink.github.io proof-size series.")
    parser.add_argument("--data", default="data/rh_shrink.json", help="output JSON path")
    parser.add_argument("--url", default=DATA_URL)
    args = parser.parse_args()

    out_path = Path(args.data)
    try:
        payload = normalize(get_json(args.url))
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as exc:
        if out_path.exists():
            print(f"Fetch failed ({exc}); keeping previous {out_path}.")
            return
        raise SystemExit(f"Fetch failed and no previous data at {out_path}: {exc}")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    previous = out_path.read_text(encoding="utf-8") if out_path.exists() else None
    if previous == text:
        print(f"No change in {out_path} (latest {payload['latest']['sha'][:9]}).")
        return
    out_path.write_text(text, encoding="utf-8", newline="\n")
    latest = payload["latest"]
    print(
        f"Wrote {out_path}: {payload['commits_measured']} commits, latest {latest['sha'][:9]} "
        f"code {latest['code']:,} ({payload['code_left_pct']}% of original), "
        f"{len(payload['recent_changes'])} recent code changes."
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Fetch the Bohrium Playground Riemann Hypothesis proof-compression board.

Public read-only JSON endpoints behind https://riemann.verifytask.cn/:
  /api/board     live board: 39 core pillars, attempts, kept techniques,
                 per-challenge run history and model x harness telemetry
  /api/timeline  curated community timeline (Playground launches + upstream PRs)

The board is normalized into data/verifytask_board.json: one row per core pillar
(baseline -> best tokens, reduction factor, score, attempt count, last kept
breakthrough + technique), the aggregate frontier run curve, and the timeline.
The raw ~700 KB board response is not stored. If a fetch fails, the previous
file is kept so the Pages table never blanks.

Pure Python 3.11+ stdlib only. Run:
  python scripts/fetch_verifytask.py [--data data/verifytask_board.json]
"""

import argparse
import json
import re
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

BOARD_URL = "https://riemann.verifytask.cn/api/board"
TIMELINE_URL = "https://riemann.verifytask.cn/api/timeline"
SITE_URL = "https://riemann.verifytask.cn/"
RSS_URL = "https://riemann.verifytask.cn/rss.xml"
USER_AGENT = "rh-kernel-backbone-verifytask/1.0"


def get_json(url):
    req = urllib.request.Request(
        url,
        headers={"User-Agent": USER_AGENT, "Accept": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=45) as response:
        return json.loads(response.read().decode("utf-8"))


def _num(value):
    return value if isinstance(value, (int, float)) and not isinstance(value, bool) else None


def _reduction_factor(baseline, best):
    try:
        base = float(baseline)
        low = float(best)
    except (TypeError, ValueError):
        return None
    if base <= 0 or low <= 0:
        return None
    return round(base / low, 2)


def _compact_leader(leader):
    if not isinstance(leader, dict):
        return None
    quality = leader.get("quality")
    return {
        "author": leader.get("authorName"),
        "score": _num(leader.get("score")),
        "model": leader.get("model_display"),
        "harness": leader.get("harness_display"),
        "axiom_status": leader.get("axiom_status"),
        "quality": quality.get("code") if isinstance(quality, dict) else None,
    }


def _compact_technique(technique):
    if not isinstance(technique, dict):
        return None
    return {
        "id": technique.get("id"),
        "attempt_id": technique.get("attempt_id"),
        "challenge_key": technique.get("challenge_key"),
        "title": technique.get("title_en"),
        "category": technique.get("category_en"),
        "author": technique.get("authorName"),
        "model": technique.get("model_display"),
        "harness": technique.get("harness_display"),
        "metric": technique.get("compact_metric_en"),
        "primary_pct": _num(technique.get("primary_pct")),
    }


def _compact_run(run):
    return {
        "i": run.get("run_idx"),
        "id": run.get("id"),
        "ts": run.get("ts"),
        "key": run.get("challenge_key"),
        "score": _num(run.get("score")),
        "compression_pct": _num(run.get("compression_pct")),
        "best": _num(run.get("running_best_score")),
        "best_pct": _num(run.get("running_best_pct")),
        "kept": bool(run.get("kept")),
        "author": run.get("authorName"),
        "model": run.get("model_display"),
        "harness": run.get("harness_display"),
        "method": run.get("chart_method_en"),
    }


def _last_kept(runs):
    kept = [run for run in runs if isinstance(run, dict) and run.get("kept")]
    if not kept:
        return None
    return max(kept, key=lambda run: run.get("ts") or "")


def _core_row(challenge, run_history, technique_by_attempt):
    key = challenge.get("key")
    run_meta = run_history.get(key) or {}
    runs = run_meta.get("runs") or []
    last_kept = _last_kept(runs)
    technique = None
    if last_kept:
        technique = technique_by_attempt.get(last_kept.get("id"))
    if technique is None:
        for candidate in technique_by_attempt.values():
            if candidate.get("challenge_key") == key:
                technique = candidate
                break
    baseline_tokens = _num(challenge.get("t0"))
    best_tokens = _num(challenge.get("best_tokens"))
    baseline_chars = _num(challenge.get("l0"))
    best_chars = _num(challenge.get("best_chars"))
    metric = "tokens" if best_tokens is not None else "chars"
    reduction = _reduction_factor(
        baseline_tokens if metric == "tokens" else baseline_chars,
        best_tokens if metric == "tokens" else best_chars,
    )
    last_ts = last_kept.get("ts") if last_kept else (runs[-1].get("ts") if runs else None)
    return {
        "key": key,
        "code": challenge.get("code"),
        "title": challenge.get("title_en"),
        "short": challenge.get("short_en"),
        "target": challenge.get("statement_math"),
        "metric": metric,
        "url": challenge.get("url"),
        "baseline_tokens": baseline_tokens,
        "best_tokens": best_tokens,
        "baseline_chars": baseline_chars,
        "best_chars": best_chars,
        "token_saved_pct": _num(challenge.get("token_saved_pct")),
        "char_saved_pct": _num(challenge.get("char_saved_pct")),
        "reduction_factor": reduction,
        "score": _num(challenge.get("top_score")),
        "attempts": challenge.get("subs"),
        "scored_attempts": challenge.get("scored_subs"),
        "participants": challenge.get("participants_count"),
        "runs": run_meta.get("total_runs") or len(runs),
        "kept_runs": run_meta.get("kept_count"),
        "leader": _compact_leader(challenge.get("leader")),
        "last_kept": (
            {
                "ts": last_kept.get("ts"),
                "attempt_id": last_kept.get("id"),
                "author": last_kept.get("authorName"),
                "model": last_kept.get("model_display"),
                "harness": last_kept.get("harness_display"),
                "score": _num(last_kept.get("score")),
                "compression_pct": _num(last_kept.get("compression_pct")),
                "method": last_kept.get("chart_method_en"),
                "technique": technique.get("title_en") if technique else None,
                "technique_url": challenge.get("url"),
            }
            if last_kept
            else None
        ),
        "last_update": last_ts,
        "technique": _compact_technique(technique),
    }


def normalize(board, timeline):
    summary = board.get("summary") or {}
    progress = board.get("progress") or {}
    core_progress = progress.get("core") or {}
    autoresearch = board.get("autoresearch") or {}
    run_history = autoresearch.get("by_challenge") or {}
    overall = autoresearch.get("overall_core") or {}

    techniques = [t for t in (board.get("techniques") or []) if isinstance(t, dict)]
    technique_by_attempt = {
        t.get("attempt_id"): t for t in techniques if t.get("attempt_id") is not None
    }

    challenges = [c for c in (board.get("challenges") or []) if isinstance(c, dict)]
    cores = [
        _core_row(challenge, run_history, technique_by_attempt)
        for challenge in challenges
        if challenge.get("tier") == "core"
    ]

    def _core_number(row):
        match = re.match(r"core(\d+)", row.get("key") or "")
        return int(match.group(1)) if match else 9999

    cores.sort(key=_core_number)

    timeline_items = []
    for item in (timeline or {}).get("items") or []:
        if not isinstance(item, dict):
            continue
        timeline_items.append(
            {
                "id": item.get("id"),
                "ts": item.get("ts"),
                "source": item.get("source"),
                "tag": item.get("tag_en") or item.get("tag_zh"),
                "title": item.get("title_en") or item.get("title_zh"),
                "summary": item.get("summary_en") or item.get("summary_zh"),
                "url": item.get("url"),
                "highlight": bool(item.get("highlight")),
            }
        )

    return {
        "source": BOARD_URL,
        "site": SITE_URL,
        "rss": RSS_URL,
        "revision": board.get("revision"),
        "updated_at": board.get("updated_at"),
        "snapshot_source": board.get("snapshot_source"),
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "summary": {
            "participants": summary.get("total_participants"),
            "scored_participants": summary.get("scored_participants"),
            "submissions": summary.get("total_submissions"),
            "scored_submissions": summary.get("scored_submissions"),
            "evaluating": summary.get("evaluating_count"),
            "core_solved": summary.get("core_solved"),
            "core_total": summary.get("core_total"),
            "verified_leaders_clean": summary.get("verified_leaders_clean"),
            "verified_leaders_total": summary.get("verified_leaders_total"),
            "techniques_count": summary.get("techniques_count"),
            "models_observed": len(summary.get("models_observed") or []),
            "harnesses_observed": len(summary.get("harnesses_observed") or []),
            "main_verification_status": summary.get("main_verification_status"),
        },
        "progress": {
            "baseline_tokens": _num(core_progress.get("baseline_tokens")),
            "best_tokens": _num(core_progress.get("current_best_tokens")),
            "saved_tokens_pct": _num(core_progress.get("saved_tokens_pct")),
            "baseline_chars": _num(core_progress.get("baseline_chars")),
            "best_chars": _num(core_progress.get("current_best_chars")),
            "saved_chars_pct": _num(core_progress.get("saved_chars_pct")),
            "solved": core_progress.get("solved_count"),
            "challenges": core_progress.get("challenge_count"),
            "tokens_measured": core_progress.get("tokens_measured_count"),
            "tokens_total": core_progress.get("tokens_total_count"),
        },
        "frontier": {
            "title": overall.get("title_en"),
            "total_runs": overall.get("total_runs"),
            "kept_count": overall.get("kept_count"),
            "current_best_score": _num(overall.get("current_best_score")),
            "current_best_pct": _num(overall.get("current_best_pct")),
            "points": [_compact_run(run) for run in (overall.get("runs") or []) if isinstance(run, dict)],
        },
        "cores": cores,
        "techniques": [_compact_technique(t) for t in techniques],
        "timeline": timeline_items,
    }


def main():
    parser = argparse.ArgumentParser(description="Fetch the riemann.verifytask.cn RH core board.")
    parser.add_argument("--data", default="data/verifytask_board.json", help="output JSON path")
    parser.add_argument("--board-url", default=BOARD_URL)
    parser.add_argument("--timeline-url", default=TIMELINE_URL)
    args = parser.parse_args()

    out_path = Path(args.data)
    try:
        board = get_json(args.board_url)
        try:
            timeline = get_json(args.timeline_url)
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as exc:
            print(f"Timeline fetch failed ({exc}); keeping board without timeline.")
            timeline = {}
        payload = normalize(board, timeline)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as exc:
        if out_path.exists():
            print(f"Fetch failed ({exc}); keeping previous {out_path}.")
            return
        raise SystemExit(f"Fetch failed and no previous data at {out_path}: {exc}")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    cores = payload["cores"]
    with_tokens = sum(1 for core in cores if core.get("best_tokens") is not None)
    print(
        f"Wrote {out_path} ({len(cores)} core pillars, {with_tokens} with measured tokens, "
        f"{len(payload['frontier']['points'])} frontier points, {len(payload['timeline'])} timeline items)."
    )


if __name__ == "__main__":
    main()

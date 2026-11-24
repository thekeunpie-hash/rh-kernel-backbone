#!/usr/bin/env python3
"""Pre-submit gate for Bohrium Playground RH core pillars (stdlib only).

Refuses a submission unless the predicted score beats the best score the
challenge's public attempts API reports right now. Fails closed: if the live
best cannot be read, the answer is HOLD. Every decision is appended to a JSONL
ledger so a held or submitted attempt leaves a record.

Exit codes: 0 = SUBMIT_OK, 3 = HOLD (improve first), 2 = board unreadable (HOLD).
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import urllib.request
from datetime import datetime, timezone

API = "https://play.bohrium.com/api/challenges/{cid}/attempts?page={page}&limit=100"
UA = "rh-kernel-backbone-submit-gate/1"
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_LEDGER = os.path.join(REPO, "data", "playground_submissions.jsonl")


def score_from_tokens(t: float, t0: float) -> float:
    """Anti-code-golf formula from the challenge statement (T0 = 50-point baseline)."""
    if t <= 0:
        return 0.0
    if t <= t0:
        return 100 - 50 / (1 + 0.5 * math.log10(t0 / t))
    return 50 / (1 + 0.5 * math.log10(t / t0))


def tokens_needed(best: float, t0: float) -> float:
    """Official token count whose score equals `best`; any shorter proof scores above it."""
    if best >= 100:
        return 0.0
    if best <= 0:
        return math.inf
    if best < 50:
        return t0 * 10 ** (2 * (50 / best - 1))  # T > T0 branch: s = 50 / (1 + 0.5 log10(T/T0))
    return t0 / 10 ** (2 * (50 / (100 - best) - 1))


def fetch_json(url: str, timeout: float) -> dict:
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def live_best(cid: str, timeout: float = 30.0, max_pages: int = 50) -> dict:
    """Read every attempt page; best = highest final displayScore among scored attempts."""
    seen, best, total = set(), None, None
    for page in range(1, max_pages + 1):
        d = fetch_json(API.format(cid=cid, page=page), timeout)
        rows = d.get("attempts") or []
        total = d.get("total", total)
        new = [a for a in rows if a.get("id") not in seen]
        if not new:
            break
        for a in new:
            seen.add(a.get("id"))
            st = a.get("scoringState") or {}
            sc = st.get("displayScore")
            if a.get("status") == "scored" and st.get("state") == "final" and isinstance(sc, (int, float)):
                if best is None or sc > best["score"]:
                    best = {"score": float(sc), "attempt_id": a.get("id"), "author": a.get("author_name"),
                            "model": a.get("modelTag"), "harness": a.get("harness")}
        if total is not None and len(seen) >= int(total):
            break
    if best is None:
        raise RuntimeError("no final scored attempt found")
    best["attempts_read"], best["attempts_total"] = len(seen), total
    return best


def decide(predicted: float, best: dict | None, t0: float, margin: float) -> dict:
    if best is None:
        return {"decision": "HOLD", "reason": "board_unreadable"}
    need = best["score"] + margin
    if predicted > need:
        return {"decision": "SUBMIT_OK", "reason": f"predicted {predicted:.4f} > best {best['score']:.4f}+{margin}"}
    return {"decision": "HOLD", "reason": f"predicted {predicted:.4f} <= best {best['score']:.4f}+{margin}",
            "improve": {"target_official_tokens_below": max(0, math.ceil(tokens_needed(need, t0)) - 1),
                        "score_gap": round(need - predicted, 4)}}


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--challenge-id", required=True)
    p.add_argument("--tokens", type=float, required=True, help="our normalized token count of the submission")
    p.add_argument("--t0", type=float, required=True, help="official 50-point baseline tokens from the statement")
    p.add_argument("--local-baseline", type=float, default=0,
                   help="our counter's count of the original closure; scales --tokens to official units")
    p.add_argument("--predicted", type=float, action="append", default=[],
                   help="other score predictions (e.g. Harbor); the gate uses the lowest")
    p.add_argument("--margin", type=float, default=0.0)
    p.add_argument("--ledger", default=DEFAULT_LEDGER)
    p.add_argument("--board-json", help="test only: read attempts from a saved file instead of the API")
    a = p.parse_args(argv)

    official = a.tokens * (a.t0 / a.local_baseline) if a.local_baseline > 0 else a.tokens
    preds = [score_from_tokens(official, a.t0)] + list(a.predicted)
    predicted = min(preds)
    try:
        if a.board_json:
            with open(a.board_json, encoding="utf-8") as f:
                rows = json.load(f)["attempts"]
            fin = [r for r in rows if r.get("status") == "scored"
                   and (r.get("scoringState") or {}).get("state") == "final"]
            top = max(fin, key=lambda r: r["scoringState"]["displayScore"])
            best = {"score": float(top["scoringState"]["displayScore"]), "attempt_id": top["id"],
                    "author": top.get("author_name"), "attempts_read": len(rows), "attempts_total": len(rows)}
        else:
            best = live_best(a.challenge_id)
        err = None
    except Exception as e:  # fail closed
        best, err = None, f"{type(e).__name__}: {e}"[:200]
    out = {"at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "challenge_id": a.challenge_id,
           "tokens_local": a.tokens, "tokens_official_est": round(official), "predicted": round(predicted, 4),
           "predictions": [round(x, 4) for x in preds], "best": best, "board_error": err}
    out.update(decide(predicted, best, a.t0, a.margin))
    os.makedirs(os.path.dirname(os.path.abspath(a.ledger)), exist_ok=True)
    with open(a.ledger, "a", encoding="utf-8") as f:
        f.write(json.dumps(out, ensure_ascii=False) + "\n")
    print(json.dumps(out, ensure_ascii=False))
    if out["decision"] == "SUBMIT_OK":
        return 0
    return 2 if best is None else 3


if __name__ == "__main__":
    sys.exit(main())

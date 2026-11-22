#!/usr/bin/env python3
"""Live auto-updating tracker for leanprover-community/riemann-hypothesis.

Designed to run locally OR inside GitHub Actions (hourly / on push / manual dispatch).
Computes exact source metrics (files, lines, import lines, declaration counts, option counts)
directly from the official repository tree (shallow clone or local repo path), fetches the
merged PR compression frontier & active stacked v4.36 PR queue via GitHub API, preserves
curated Verified Pattern diffs/receipts and Kernel-Cone Actionable Targets, and writes
`data/upstream_frontier.json` (plus appends a timestamped point to `live_history`).
"""

import argparse
import json
import os
import re
import subprocess
import tempfile
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

UPSTREAM_REPO = "leanprover-community/riemann-hypothesis"
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s+)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|meta|public|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\b"
)
IMPORT_RE = re.compile(r"^(?:public\s+|meta\s+)?import\s+")
BACKWARD_RE = re.compile(r"set_option\s+backward\.")
HEARTBEAT_RE = re.compile(r"set_option\s+(?:synthInstance\.)?maxHeartbeats\b")

# Curated category/metadata overrides for landmark upstream PRs so frontier charts stay crisp.
PR_META = {
    8: ("dead-prune", "dead", 6, "Simplify Main imports and remove 6 unused modules"),
    45: ("dead-prune", "dead", 10718, "Prune unused top-level imports and 10,718 unreachable dead modules"),
    57: ("active-refactor", "active", 0, "Simplify pp.explicit dumps in 5 CapelliIdentities files"),
    60: ("active-refactor", "active", 0, "De-explicitize FixPiIff.lean (8,029 -> 45 L, -99.5% norm tokens)"),
    65: ("active-refactor", "active", 0, "De-explicitize 4 kernel-used CapelliIdentities files (105 -> 0 warnings)"),
    68: ("active-refactor", "active", 0, "Share rank-induction proof of GL finiteness across 182 files (-9,010 L)"),
    71: ("portability", "active", 0, "Remove 66 backward.* options across 4 kernel-used scheme files (ported in #91)"),
    66: ("toolchain-prune", "mixed", 15068, "Bump to Lean & Mathlib v4.36.0, module system, prune 15,068 dead files"),
    91: ("active-refactor", "active", 0, "Combine 10+ reviewed cleanups on Lean 4.36 (incl. #70, #71, #74-#76, #80-#82, #90)"),
    62: ("active-refactor", "active", 0, "Shorten machine-dumped terms & reuse repeated proofs in 76 modules (v4.36)"),
    79: ("portability", "active", 0, "Remove heartbeat overrides across v4.36 tree"),
    98: ("portability", "active", 0, "Minimize and privatize imports on Lean 4.36"),
    88: ("verification", "statement", 0, "DeepMind formal-conjectures Comparator setup (con-leche --compare ACCEPTED)"),
    97: ("formatting", "full", 0, "Run Lean auto-formatter over 147,418 files in src/ (v4.36)"),
    63: ("architecture", "full", 110371, "Consolidate 133,202 small sibling modules into 22,831 antichain bundles"),
    83: ("active-refactor", "active", 0, "Zero-free region: replace 34-file assembly with 2,368-token proof (-89.1%)"),
    87: ("active-refactor", "active", 0, "Shorten checked proofs across 816 Lean modules"),
    101: ("infra", "full", 0, "Let registered donors build bounded proof shards"),
    104: ("performance", "active", 0, "Speed up the slowest proofs (stacked on #79)"),
    109: ("active-refactor", "active", 180, "Restore #68 shared GL finiteness proof on Lean 4.36 (-180 files, -9,730 L)"),
    110: ("active-refactor", "active", 0, "Simplify explicit type dumps in cpR and std_cpR (NonzeroPlacesOverPrimesOfLifts.lean, -71.2% norm tokens)"),
}

TRACKED_OPEN_PRS = [109, 110, 91, 62, 79, 98, 104, 88, 97, 63, 83, 87, 101, 71]


def gh_api(path: str, token: str = ""):
    headers = {
        "User-Agent": "rh-kernel-backbone-tracker/2.0",
        "Accept": "application/vnd.github+json",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(f"https://api.github.com/{path}", headers=headers)
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"))


def scan_lean_tree(repo_dir: Path, ref: str = "") -> dict:
    """Count exact .lean files, lines, import lines, decl headers, backward.* and maxHeartbeats."""
    lean_files = 0
    total_lines = 0
    import_lines = 0
    decl_count = 0
    backward_opts = 0
    heartbeat_opts = 0
    total_bytes = 0
    toolchain = ""
    head_sha = ""
    head_date = ""

    if ref:
        toolchain = subprocess.check_output(
            ["git", "-C", str(repo_dir), "show", f"{ref}:lean-toolchain"],
            text=True,
        ).strip()
        head_info = subprocess.check_output(
            ["git", "-C", str(repo_dir), "show", "-s", "--format=%H %cI", ref],
            text=True,
        ).strip().split(" ", 1)
        head_sha, head_date = head_info[0][:9], head_info[1]
        # Stream all src/**/*.lean via git archive for speed without touching working tree
        proc = subprocess.Popen(
            ["git", "-C", str(repo_dir), "archive", "--format=tar", ref, "src"],
            stdout=subprocess.PIPE,
        )
        import tarfile

        with tarfile.open(fileobj=proc.stdout, mode="r|") as tf:
            for member in tf:
                if not member.isfile() or not member.name.endswith(".lean"):
                    continue
                f = tf.extractfile(member)
                if f is None:
                    continue
                raw = f.read()
                lean_files += 1
                total_bytes += len(raw)
                text = raw.decode("utf-8", "ignore")
                lines = text.splitlines()
                total_lines += len(lines)
                for line in lines:
                    s = line.lstrip()
                    if not s:
                        continue
                    if IMPORT_RE.match(s):
                        import_lines += 1
                    elif DECL_RE.match(s):
                        decl_count += 1
                    if "set_option" in s:
                        if BACKWARD_RE.search(s):
                            backward_opts += 1
                        if HEARTBEAT_RE.search(s):
                            heartbeat_opts += 1
        proc.wait()
        if proc.returncode != 0:
            raise RuntimeError(f"git archive failed with code {proc.returncode}")
    else:
        tc_path = repo_dir / "lean-toolchain"
        if tc_path.is_file():
            toolchain = tc_path.read_text(encoding="utf-8").strip()
        try:
            head_info = subprocess.check_output(
                ["git", "-C", str(repo_dir), "show", "-s", "--format=%H %cI", "HEAD"],
                text=True,
            ).strip().split(" ", 1)
            head_sha, head_date = head_info[0][:9], head_info[1]
        except Exception:
            pass
        src_root = repo_dir / "src"
        for p in src_root.rglob("*.lean"):
            raw = p.read_bytes()
            lean_files += 1
            total_bytes += len(raw)
            lines = raw.decode("utf-8", "ignore").splitlines()
            total_lines += len(lines)
            for line in lines:
                s = line.lstrip()
                if not s:
                    continue
                if IMPORT_RE.match(s):
                    import_lines += 1
                elif DECL_RE.match(s):
                    decl_count += 1
                if "set_option" in s:
                    if BACKWARD_RE.search(s):
                        backward_opts += 1
                    if HEARTBEAT_RE.search(s):
                        heartbeat_opts += 1

    return {
        "sha": head_sha,
        "commit_date": head_date,
        "toolchain": toolchain,
        "lean_files": lean_files,
        "total_lines": total_lines,
        "total_bytes": total_bytes,
        "import_lines": import_lines,
        "declarations": decl_count,
        "backward_options": backward_opts,
        "heartbeat_options": heartbeat_opts,
    }


def fetch_pr_queue(token: str, extra_nums: list[int] | None = None) -> tuple[list, int]:
    """Fetch open PR count and detailed status of tracked/landmark PRs."""
    open_list = gh_api(f"repos/{UPSTREAM_REPO}/pulls?state=open&per_page=100", token)
    open_count = len(open_list)
    nums = list(TRACKED_OPEN_PRS)
    for n in extra_nums or []:
        if n not in nums:
            nums.append(n)
    # Also surface any open PR authored by thekeunpie-hash automatically
    for p in open_list:
        if p.get("user", {}).get("login") == "thekeunpie-hash" and p["number"] not in nums:
            nums.insert(0, p["number"])

    queue = []
    for num in nums:
        try:
            pr = gh_api(f"repos/{UPSTREAM_REPO}/pulls/{num}", token)
        except Exception:
            continue
        cat, scope, _, default_title = PR_META.get(num, ("active-refactor", "active", 0, ""))
        state = "merged" if pr.get("merged_at") else pr.get("state", "open")
        if num == 71 and state == "open":
            state = "batched"
        add = pr.get("additions", 0)
        dels = pr.get("deletions", 0)
        queue.append(
            {
                "pr": num,
                "state": state,
                "draft": bool(pr.get("draft")),
                "author": pr["user"]["login"],
                "category": cat,
                "scope": scope,
                "title": default_title or pr["title"],
                "raw_title": pr["title"],
                "changed_files": pr.get("changed_files", 0),
                "additions": add,
                "deletions": dels,
                "net_lines": add - dels,
                "updated_at": pr.get("updated_at", ""),
                "merged_at": pr.get("merged_at"),
                "url": pr["html_url"],
            }
        )
    return queue, open_count


def main():
    parser = argparse.ArgumentParser(description="Update rh-kernel-backbone live upstream tracker JSON.")
    parser.add_argument("--data", type=Path, default=Path("data/upstream_frontier.json"))
    parser.add_argument("--upstream-repo", type=Path, default=None, help="Existing local clone of upstream RH repo")
    parser.add_argument("--upstream-ref", default="", help="Git ref in --upstream-repo (e.g. origin/main)")
    parser.add_argument("--skip-api", action="store_true", help="Skip GitHub API calls for open PR queue")
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN", "")
    existing = json.loads(args.data.read_text(encoding="utf-8")) if args.data.exists() else {}

    if args.upstream_repo is not None:
        live_main = scan_lean_tree(args.upstream_repo, ref=args.upstream_ref)
    else:
        with tempfile.TemporaryDirectory(prefix="rh-upstream-shallow-") as td:
            subprocess.check_call(
                ["git", "clone", "--depth", "1", "--no-checkout", f"https://github.com/{UPSTREAM_REPO}.git", td]
            )
            live_main = scan_lean_tree(Path(td), ref="HEAD")

    now_iso = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    prev_live = dict(existing.get("live_main") or {})
    prev_live.pop("measured_at", None)
    prev_history = existing.get("live_history") or []
    prev_queue = existing.get("stacked_pr_queue") or []

    new_live_no_ts = {
        **live_main,
        "files_delta_vs_v021": live_main["lean_files"] - existing.get("baseline_files", 175187),
        "lines_delta_vs_v021": live_main["total_lines"] - existing.get("baseline_raw_lines", 17374215),
    }
    if "open_pr_count" in prev_live:
        new_live_no_ts["open_pr_count"] = prev_live["open_pr_count"]

    # Append/dedupe snapshot history by commit sha so time-series grows automatically on every main merge.
    history = list(prev_history)
    if not history:
        history.append(
            {
                "date": "2026-11-21T07:54:00Z",
                "sha": "06c2690c1",
                "label": "v0.2.1 Baseline",
                "toolchain": "leanprover/lean4:v4.33.1",
                "lean_files": 175187,
                "total_lines": 17374215,
                "declarations": 1063284,
                "import_lines": None,
            }
        )
    if not any(h.get("sha") == live_main["sha"] for h in history):
        history.append(
            {
                "date": live_main["commit_date"] or now_iso,
                "sha": live_main["sha"],
                "label": f"main@{live_main['sha']}",
                "toolchain": live_main["toolchain"],
                "lean_files": live_main["lean_files"],
                "total_lines": live_main["total_lines"],
                "declarations": live_main["declarations"],
                "import_lines": live_main["import_lines"],
                "backward_options": live_main["backward_options"],
                "heartbeat_options": live_main["heartbeat_options"],
            }
        )

    new_queue = prev_queue
    if not args.skip_api:
        try:
            queue, open_count = fetch_pr_queue(token)
            new_live_no_ts["open_pr_count"] = open_count
            if queue:
                new_queue = queue
        except Exception as exc:
            print(f"Warning: GitHub API queue fetch skipped ({exc})")

    if new_live_no_ts == prev_live and history == prev_history and new_queue == prev_queue:
        print(f"No upstream metric or PR queue changes at main@{live_main['sha']}; skipping write.")
        return

    existing["generated_at"] = now_iso
    existing["live_main"] = {**new_live_no_ts, "measured_at": now_iso}
    existing["live_history"] = history
    if new_queue:
        existing["stacked_pr_queue"] = new_queue

    args.data.write_text(json.dumps(existing, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(
        f"Updated {args.data}: main@{live_main['sha']} ({live_main['toolchain']}) | "
        f"{live_main['lean_files']:,} files | {live_main['total_lines']:,} lines | "
        f"{live_main['import_lines']:,} imports | {live_main['declarations']:,} decls | "
        f"{live_main['backward_options']:,} backward.* | {live_main['heartbeat_options']:,} maxHeartbeats"
    )


if __name__ == "__main__":
    main()

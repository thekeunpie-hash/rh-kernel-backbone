#!/usr/bin/env python3
"""Audit and reproduce the aggregation scopes of docs/data/editions.json.

Pure Python 3.11+ standard library. Supports three layers of verification:

1. Standalone repository audit (default; requires no external downloads):
   Verifies that docs/data/editions.json compares every edition on matching units
   and scopes, stays consistent with data/kernel_backbone_summary.json, SPEC.md,
   and docs/tracker.html, and passes all internal arithmetic and pairing checks.

2. Optional Alpoge v0.2.1 kernel-export reproduction (--alpoge-export DIR):
   Recomputes Alpoge archive totals, proof-cone declarations, proof-cone
   declaration lines, and project-only vs. full proof-cone constants directly
   from Andrew Sutherland / James Shore's directories.csv.gz, decls.csv.gz, and
   constants.csv.gz.

3. Optional Lean source-tree reproduction (--tree EDITION_ID=SRC_DIR):
   Recomputes all nine static source metrics (files, raw lines, comment/blank-
   stripped code lines, UTF-8 bytes, non-whitespace code characters, Lean tokens,
   characters per code line, semicolons per 1,000 code lines, longest line) from
   a local Lean src/ tree and checks exact parity against docs/data/editions.json.
"""
from __future__ import annotations

import argparse
import csv
from collections import Counter
from datetime import datetime
import gzip
import json
import math
from pathlib import Path
import re
import sys
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent

REQUIRED_EDITIONS = ("alpoge_v021", "grh_readable", "grh_compact", "grh_clean")
VALID_FMTS = {"int", "dec", "bytes", "dur"}
ALPOGE_ARCHIVE_ROWS = frozenset({"Files", "Raw lines", "Source size"})

TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|\d+|[^\sA-Za-z0-9_]")
SEMI_RE = re.compile(r";")

SPEC_CONE_RE = re.compile(
    r"`(?P<full>[\d,]+)`\s+kernel constants\s*\(`cone-constants\.txt\.gz`\):\s*"
    r"`(?P<project>[\d,]+)`\s+project,\s*"
    r"`(?P<mathlib>[\d,]+)`\s+Mathlib,\s*"
    r"`(?P<core>[\d,]+)`\s+Lean core,\s*"
    r"`(?P<batteries>[\d,]+)`\s+Batteries,\s*"
    r"`(?P<aesop>[\d,]+)`\s+Aesop"
)

TRACKER_CONE_RE = re.compile(
    r"full kernel cone is\s+(?P<full>[\d,]+)\s+constants,\s+of which\s+(?P<libs>[\d,]+)\s+come from those libraries"
)

TREE_ROW_KEYS = (
    ("Files", "files"),
    ("Raw lines", "raw_lines"),
    ("Code lines (no comments or blanks)", "code_lines"),
    ("Source size", "bytes"),
    ("Non-whitespace code characters", "non_ws"),
    ("Lean tokens", "tokens"),
    ("Non-whitespace characters per code line", "avg_non_ws_per_code_line"),
    ("Semicolons per 1,000 code lines", "semis_per_1k_code_lines"),
    ("Longest line (characters)", "max_line_len"),
)


def _parse_int(token: str) -> int:
    return int(token.replace(",", ""))


def _is_finite_number(val: Any) -> bool:
    return isinstance(val, (int, float)) and not isinstance(val, bool) and math.isfinite(val)


def _open_maybe_gz(path: Path):
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8", newline="")
    return path.open("rt", encoding="utf-8", newline="")


def _resolve_export_file(export_dir: Path, stem: str) -> Path:
    for name in (f"{stem}.csv.gz", f"{stem}.csv"):
        candidate = export_dir / name
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"Missing {stem}.csv.gz (or {stem}.csv) under {export_dir}")


def strip_lean_comments(text: str) -> str:
    """Strip Lean 4 nested block comments (`/- ... -/`) and line comments (`-- ...`).

    Preserves string literals (with backslash escapes) and newlines so line counts
    and token counts match the edition-comparison source scanner.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth == 0 and not in_str and ch == '"':
            in_str = True
            out.append(ch)
            i += 1
        elif in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(nxt)
                i += 2
            elif ch == '"':
                in_str = False
                i += 1
            else:
                i += 1
        elif ch == "/" and nxt == "-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and ch == "-" and nxt == "/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if ch == "\n" else " ")
            i += 1
        elif ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def scan_lean_tree(src_dir: Path) -> dict[str, int | float]:
    """Measure static source metrics for a Lean src/ directory."""
    if not src_dir.is_dir():
        raise FileNotFoundError(f"Lean source directory not found: {src_dir}")
    tot: Counter[str] = Counter()
    max_line_len = 0
    for path in sorted(src_dir.rglob("*.lean")):
        raw = path.read_text(encoding="utf-8", errors="replace")
        raw_lines = raw.splitlines()
        code = strip_lean_comments(raw)
        code_lines_list = [ln for ln in code.splitlines() if ln.strip()]
        non_ws = sum(len(ln.replace(" ", "").replace("\t", "")) for ln in code_lines_list)
        tokens = len(TOKEN_RE.findall(code))
        semis = len(SEMI_RE.findall(code))
        file_max = max((len(ln) for ln in raw_lines), default=0)
        if file_max > max_line_len:
            max_line_len = file_max
        tot["files"] += 1
        tot["bytes"] += len(raw.encode("utf-8"))
        tot["raw_lines"] += len(raw_lines)
        tot["code_lines"] += len(code_lines_list)
        tot["non_ws"] += non_ws
        tot["tokens"] += tokens
        tot["semis"] += semis

    code_lines = tot["code_lines"]
    return {
        "files": tot["files"],
        "bytes": tot["bytes"],
        "raw_lines": tot["raw_lines"],
        "code_lines": code_lines,
        "non_ws": tot["non_ws"],
        "tokens": tot["tokens"],
        "semis": tot["semis"],
        "max_line_len": max_line_len,
        "avg_non_ws_per_code_line": round(tot["non_ws"] / code_lines, 2) if code_lines else 0.0,
        "semis_per_1k_code_lines": round(tot["semis"] * 1000.0 / code_lines, 2) if code_lines else 0.0,
    }


def reproduce_alpoge_export(export_dir: Path) -> dict[str, Any]:
    """Recompute Alpoge v0.2.1 archive and proof-cone totals from kernel export CSVs."""
    dirs_path = _resolve_export_file(export_dir, "directories")
    decls_path = _resolve_export_file(export_dir, "decls")
    consts_path = _resolve_export_file(export_dir, "constants")

    top_dirs: list[str] = []
    dir_files = 0
    dir_raw_lines = 0
    dir_cone_decls = 0
    dir_cone_lines = 0
    with _open_maybe_gz(dirs_path) as fh:
        for row in csv.DictReader(fh):
            if row.get("level") == "1":
                top_dirs.append(row["dir"])
                dir_files += int(row["files"])
                dir_raw_lines += int(row["lines"])
                dir_cone_decls += int(row["decls_in_cone"])
                dir_cone_lines += int(row["lines_in_cone"])

    decls_total = 0
    decls_cone = 0
    decls_cone_lines = 0
    decl_origins: Counter[str] = Counter()
    with _open_maybe_gz(decls_path) as fh:
        for row in csv.DictReader(fh):
            decls_total += 1
            decl_origins[row.get("origin", "")] += 1
            if row.get("in_cone", "").lower() == "true":
                decls_cone += 1
                decls_cone_lines += int(row["lines"])

    cone_by_origin: Counter[str] = Counter()
    with _open_maybe_gz(consts_path) as fh:
        for row in csv.DictReader(fh):
            if row.get("in_cone", "").lower() == "true":
                cone_by_origin[row.get("origin", "")] += 1

    full_cone = sum(cone_by_origin.values())
    project_cone = cone_by_origin.get("project", 0)
    return {
        "top_level_dirs": sorted(top_dirs),
        "non_src_top_dirs": sorted(d for d in top_dirs if not d.startswith("src/")),
        "files": dir_files,
        "raw_lines": dir_raw_lines,
        "directories_cone_decls": dir_cone_decls,
        "directories_cone_lines": dir_cone_lines,
        "decls_total": decls_total,
        "decl_origins": dict(decl_origins),
        "decls_in_cone": decls_cone,
        "decl_lines_in_cone": decls_cone_lines,
        "cone_constants_by_origin": dict(cone_by_origin),
        "project_cone_constants": project_cone,
        "full_cone_constants": full_cone,
        "library_cone_constants": full_cone - project_cone,
    }


def _check_spec_breakdown(spec_text: str, errors: list[str]) -> dict[str, int] | None:
    match = SPEC_CONE_RE.search(spec_text)
    if not match:
        errors.append("SPEC.md: could not parse Alpoge proof-cone origin breakdown in section 1")
        return None
    parts = {k: _parse_int(v) for k, v in match.groupdict().items()}
    libs = parts["mathlib"] + parts["core"] + parts["batteries"] + parts["aesop"]
    if parts["project"] + libs != parts["full"]:
        errors.append(
            f"SPEC.md: origin breakdown sum ({parts['project']} + {libs}) != full cone ({parts['full']})"
        )
    parts["libraries"] = libs
    return parts


def audit_editions(
    editions_path: Path,
    summary_path: Path,
    spec_path: Path,
    tracker_path: Path,
    alpoge_export_dir: Path | None = None,
    tree_specs: list[tuple[str, Path]] | None = None,
) -> dict[str, Any]:
    """Run standalone scope audit plus optional kernel-export and source-tree reproduction."""
    errors: list[str] = []
    checks: list[str] = []

    editions = json.loads(editions_path.read_text(encoding="utf-8"))
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    spec_text = spec_path.read_text(encoding="utf-8")
    tracker_text = tracker_path.read_text(encoding="utf-8")

    # 1. Schema and structural integrity
    if editions.get("schema") != 1:
        errors.append(f"editions.json: expected schema == 1, got {editions.get('schema')!r}")
    ed_list = editions.get("editions")
    rows_list = editions.get("rows")
    if not isinstance(ed_list, list) or not ed_list:
        errors.append("editions.json: editions must be a non-empty list")
        return {"pass": False, "checks": checks, "errors": errors}
    if not isinstance(rows_list, list) or not rows_list:
        errors.append("editions.json: rows must be a non-empty list")
        return {"pass": False, "checks": checks, "errors": errors}

    ed_ids = [e.get("id") for e in ed_list if isinstance(e, dict)]
    ed_index = {eid: idx for idx, eid in enumerate(ed_ids)}
    for req in REQUIRED_EDITIONS:
        if req not in ed_index:
            errors.append(f"editions.json: missing required edition id {req!r}")

    rows_by_label: dict[str, dict[str, Any]] = {}
    for row in rows_list:
        label = row.get("label")
        fmt = row.get("fmt")
        values = row.get("values")
        if not isinstance(label, str) or not label:
            errors.append(f"editions.json: row missing non-empty label: {row!r}")
            continue
        if label in rows_by_label:
            errors.append(f"editions.json: duplicate row label {label!r}")
        rows_by_label[label] = row
        if fmt not in VALID_FMTS:
            errors.append(f"editions.json: row {label!r} has invalid fmt {fmt!r}")
        if not isinstance(values, list) or len(values) != len(ed_list):
            errors.append(f"editions.json: row {label!r} values length does not match editions ({len(ed_list)})")
            continue
        for idx, val in enumerate(values):
            if val is not None and (not _is_finite_number(val) or val < 0):
                errors.append(f"editions.json: row {label!r}[{idx}] must be null or non-negative finite number")
    checks.append("schema_and_row_shapes")

    def cell(label: str, edition_id: str) -> Any:
        row = rows_by_label.get(label)
        idx = ed_index.get(edition_id)
        if row is None or idx is None or not isinstance(row.get("values"), list) or idx >= len(row["values"]):
            return None
        return row["values"][idx]

    # 2. Alpoge archive scope footnote and flags
    scope_note = editions.get("alpoge_archive_scope")
    if not isinstance(scope_note, str) or not scope_note.strip():
        errors.append("editions.json: missing non-empty alpoge_archive_scope")
    else:
        if "175,187" not in scope_note or "src/" not in scope_note:
            errors.append("editions.json: alpoge_archive_scope must state the 175,187-file src/ archive scope")
        if "136,266" in scope_note:
            errors.append("editions.json: alpoge_archive_scope repeats false 136,266 Mathlib files claim")
    flagged = {label for label, r in rows_by_label.items() if r.get("alpoge_archive") is True}
    if flagged != ALPOGE_ARCHIVE_ROWS:
        errors.append(
            f"editions.json: alpoge_archive=true rows {sorted(flagged)} != expected {sorted(ALPOGE_ARCHIVE_ROWS)}"
        )
    checks.append("alpoge_archive_scope_flags")

    # 3. Same-unit and same-scope guarantees across Alpoge vs grh columns
    gt = summary.get("global_totals", {})
    spec_cone = _check_spec_breakdown(spec_text, errors)

    if cell("Code lines (no comments or blanks)", "alpoge_v021") is not None:
        errors.append(
            "editions.json: Alpoge 'Code lines (no comments or blanks)' must be null "
            "(do not mix proof-cone declaration lines with full-tree code lines)"
        )

    expected_from_summary = (
        ("Files", "files_total"),
        ("Raw lines", "raw_source_lines_total"),
        ("Declaration lines in the proof cone", "decl_lines_in_cone"),
        ("Declarations in the proof cone", "decls_in_cone"),
    )
    for row_label, gt_key in expected_from_summary:
        actual = cell(row_label, "alpoge_v021")
        expected = gt.get(gt_key)
        if actual != expected:
            errors.append(
                f"editions.json: Alpoge {row_label!r}={actual!r} != "
                f"kernel_backbone_summary.json global_totals.{gt_key}={expected!r}"
            )
    checks.append("alpoge_summary_parity")

    alpoge_cone_consts = cell("Constants in the proof cone", "alpoge_v021")
    alpoge_cone_decls = cell("Declarations in the proof cone", "alpoge_v021")
    if spec_cone is not None:
        if alpoge_cone_consts == spec_cone["full"]:
            errors.append(
                f"editions.json: Alpoge 'Constants in the proof cone' uses full library-inclusive cone "
                f"({spec_cone['full']}); must use project-only count ({spec_cone['project']})"
            )
        elif alpoge_cone_consts != spec_cone["project"]:
            errors.append(
                f"editions.json: Alpoge 'Constants in the proof cone'={alpoge_cone_consts!r} != "
                f"SPEC.md project-only cone ({spec_cone['project']})"
            )
    if alpoge_cone_consts is not None and alpoge_cone_decls is not None and alpoge_cone_consts == alpoge_cone_decls:
        errors.append("editions.json: Alpoge 'Constants in the proof cone' must not equal declaration count")
    checks.append("project_only_proof_cone_scope")

    # 4. Per-edition arithmetic and monotonicity invariants
    for eid in ed_ids:
        raw_l = cell("Raw lines", eid)
        code_l = cell("Code lines (no comments or blanks)", eid)
        decl_l = cell("Declaration lines in the proof cone", eid)
        non_ws = cell("Non-whitespace code characters", eid)
        nws_per_l = cell("Non-whitespace characters per code line", eid)
        k_consts = cell("Kernel constants", eid)
        cone_consts = cell("Constants in the proof cone", eid)
        cone_decls = cell("Declarations in the proof cone", eid)

        if code_l is not None and raw_l is not None and not (0 < code_l <= raw_l):
            errors.append(f"editions.json: {eid} code_lines ({code_l}) must satisfy 0 < code_lines <= raw_lines ({raw_l})")
        if decl_l is not None and raw_l is not None and not (0 < decl_l <= raw_l):
            errors.append(f"editions.json: {eid} decl_lines ({decl_l}) must satisfy 0 < decl_lines <= raw_lines ({raw_l})")
        if code_l and non_ws is not None and nws_per_l is not None:
            expected_ratio = round(non_ws / code_l, 2)
            if abs(expected_ratio - nws_per_l) > 0.01:
                errors.append(
                    f"editions.json: {eid} non_ws/code_lines={expected_ratio} != reported {nws_per_l}"
                )
        if cone_decls is not None and cone_consts is not None and not (0 < cone_decls <= cone_consts):
            errors.append(
                f"editions.json: {eid} Declarations in the proof cone ({cone_decls}) > "
                f"Constants in the proof cone ({cone_consts})"
            )
        if cone_consts is not None and k_consts is not None and not (0 < cone_consts <= k_consts):
            errors.append(
                f"editions.json: {eid} Constants in the proof cone ({cone_consts}) > Kernel constants ({k_consts})"
            )
    checks.append("per_edition_invariants")

    # 5. Export inversion parity
    inv = editions.get("export_inversion")
    if not isinstance(inv, dict):
        errors.append("editions.json: missing export_inversion object")
    else:
        r_exp = inv.get("readable_export_bytes")
        c_exp = inv.get("compact_export_bytes")
        r_bld = inv.get("readable_build_sec")
        c_bld = inv.get("compact_build_sec")
        if r_exp != cell("Kernel export size", "grh_readable"):
            errors.append("editions.json: export_inversion.readable_export_bytes != Kernel export size[grh_readable]")
        if c_exp != cell("Kernel export size", "grh_compact"):
            errors.append("editions.json: export_inversion.compact_export_bytes != Kernel export size[grh_compact]")
        if r_bld != cell("Cold build time", "grh_readable"):
            errors.append("editions.json: export_inversion.readable_build_sec != Cold build time[grh_readable]")
        if c_bld != cell("Cold build time", "grh_compact"):
            errors.append("editions.json: export_inversion.compact_build_sec != Cold build time[grh_compact]")
        if _is_finite_number(r_exp) and _is_finite_number(c_exp) and r_exp > 0:
            calc_exp_pct = round((c_exp - r_exp) * 100.0 / r_exp, 1)
            if abs(calc_exp_pct - inv.get("compact_vs_readable_export_pct", float("nan"))) > 0.1:
                errors.append(
                    f"editions.json: export_inversion.compact_vs_readable_export_pct="
                    f"{inv.get('compact_vs_readable_export_pct')} != recomputed {calc_exp_pct}"
                )
        cl_r = cell("Code lines (no comments or blanks)", "grh_readable")
        cl_c = cell("Code lines (no comments or blanks)", "grh_compact")
        if _is_finite_number(cl_r) and _is_finite_number(cl_c) and cl_r > 0:
            calc_cl_pct = round((cl_c - cl_r) * 100.0 / cl_r, 1)
            if abs(calc_cl_pct - inv.get("compact_vs_readable_code_lines_pct", float("nan"))) > 0.1:
                errors.append(
                    f"editions.json: export_inversion.compact_vs_readable_code_lines_pct="
                    f"{inv.get('compact_vs_readable_code_lines_pct')} != recomputed {calc_cl_pct}"
                )
    checks.append("export_inversion_parity")

    # 6. Cross-repo pairing scope and timestamp ordering
    pair = editions.get("cross_repo_pairing")
    if not isinstance(pair, dict):
        errors.append("editions.json: missing cross_repo_pairing object")
    else:
        gen_ts = editions.get("generated_at")
        pair_ts = pair.get("measured_at")
        if isinstance(gen_ts, str) and isinstance(pair_ts, str):
            try:
                if datetime.fromisoformat(pair_ts) > datetime.fromisoformat(gen_ts):
                    errors.append(
                        f"editions.json: generated_at ({gen_ts}) predates cross_repo_pairing.measured_at ({pair_ts})"
                    )
            except ValueError as exc:
                errors.append(f"editions.json: invalid ISO timestamp: {exc}")
        if not isinstance(pair.get("genuine_shorter_rule"), str) or not pair["genuine_shorter_rule"].strip():
            errors.append("editions.json: cross_repo_pairing.genuine_shorter_rule must be non-empty")
        if pair.get("grh_modules") != cell("Files", "grh_readable"):
            errors.append("editions.json: cross_repo_pairing.grh_modules != Files[grh_readable]")
        if pair.get("compact_modules") != cell("Files", "grh_compact"):
            errors.append("editions.json: cross_repo_pairing.compact_modules != Files[grh_compact]")
        if pair.get("common_path_modules", -1) + pair.get("grh_only_total", -1) != pair.get("grh_modules"):
            errors.append("editions.json: common_path_modules + grh_only_total != grh_modules")
        if pair.get("common_path_modules", -1) + pair.get("compact_only_total", -1) != pair.get("compact_modules"):
            errors.append("editions.json: common_path_modules + compact_only_total != compact_modules")
        accepted = pair.get("non_identical_pairs_accepted", -1)
        if not (accepted <= pair.get("grh_only_covered", -1) <= pair.get("grh_only_total", -1)):
            errors.append("editions.json: grh_only_covered out of [non_identical_pairs_accepted, grh_only_total]")
        if not (accepted <= pair.get("compact_only_covered", -1) <= pair.get("compact_only_total", -1)):
            errors.append("editions.json: compact_only_covered out of [non_identical_pairs_accepted, compact_only_total]")
        if not (
            pair.get("high_confidence_1to1_genuine_shorter", -1)
            <= pair.get("high_confidence_genuine_shorter", -1)
            <= pair.get("high_confidence_pairs", -1)
            <= accepted
        ):
            errors.append("editions.json: high_confidence counts violate subset ordering")
        ref_sum = (
            pair.get("references_unplaced_high", -1)
            + pair.get("references_unplaced_medium", -1)
            + pair.get("references_unplaced_low", -1)
        )
        if ref_sum != pair.get("references_unplaced"):
            errors.append("editions.json: references_unplaced_{high,medium,low} sum != references_unplaced")
        if pair.get("references_unplaced", 0) > pair.get("references_total", -1):
            errors.append("editions.json: references_unplaced > references_total")
        if pair.get("tauceti_candidate_theorems", 0) > pair.get("tauceti_candidates", -1):
            errors.append("editions.json: tauceti_candidate_theorems > tauceti_candidates")
    checks.append("cross_repo_pairing_scope")

    # 7. docs/tracker.html caption and renderer parity
    if "./data/editions.json" not in tracker_text:
        errors.append("docs/tracker.html: missing fetch of ./data/editions.json")
    if "alpoge_archive_scope" not in tracker_text:
        errors.append("docs/tracker.html: missing alpoge_archive_scope footnote wiring")
    if "136,266 Mathlib" in tracker_text:
        errors.append("docs/tracker.html: contains false '136,266 Mathlib' archive claim")
    tracker_match = TRACKER_CONE_RE.search(tracker_text)
    if not tracker_match:
        errors.append("docs/tracker.html: missing Alpoge full-cone / library-constants caption")
    elif spec_cone is not None:
        t_full = _parse_int(tracker_match.group("full"))
        t_libs = _parse_int(tracker_match.group("libs"))
        if t_full != spec_cone["full"] or t_libs != spec_cone["libraries"]:
            errors.append(
                f"docs/tracker.html: caption full={t_full}, libs={t_libs} != "
                f"SPEC.md full={spec_cone['full']}, libs={spec_cone['libraries']}"
            )
    checks.append("tracker_caption_parity")

    reproduced: dict[str, Any] = {}

    # 8. Optional direct Alpoge v0.2.1 kernel-export reproduction
    if alpoge_export_dir is not None:
        rep = reproduce_alpoge_export(alpoge_export_dir)
        reproduced["alpoge_export"] = rep
        if rep["non_src_top_dirs"]:
            errors.append(f"alpoge-export: non-src/ top-level directories found: {rep['non_src_top_dirs']}")
        if rep["directories_cone_decls"] != rep["decls_in_cone"]:
            errors.append(
                f"alpoge-export: directories.csv decls_in_cone ({rep['directories_cone_decls']}) != "
                f"decls.csv ({rep['decls_in_cone']})"
            )
        if rep["directories_cone_lines"] != rep["decl_lines_in_cone"]:
            errors.append(
                f"alpoge-export: directories.csv lines_in_cone ({rep['directories_cone_lines']}) != "
                f"decls.csv ({rep['decl_lines_in_cone']})"
            )
        if set(rep["decl_origins"].keys()) != {"project"}:
            errors.append(f"alpoge-export: unexpected decls.csv origins: {rep['decl_origins']}")
        for row_label, rep_key in (
            ("Files", "files"),
            ("Raw lines", "raw_lines"),
            ("Declaration lines in the proof cone", "decl_lines_in_cone"),
            ("Constants in the proof cone", "project_cone_constants"),
            ("Declarations in the proof cone", "decls_in_cone"),
        ):
            actual = cell(row_label, "alpoge_v021")
            if actual != rep[rep_key]:
                errors.append(
                    f"alpoge-export: editions.json Alpoge {row_label!r}={actual!r} != reproduced {rep[rep_key]!r}"
                )
        if spec_cone is not None:
            if rep["full_cone_constants"] != spec_cone["full"]:
                errors.append(
                    f"alpoge-export: reproduced full cone {rep['full_cone_constants']} != SPEC.md {spec_cone['full']}"
                )
            if rep["library_cone_constants"] != spec_cone["libraries"]:
                errors.append(
                    f"alpoge-export: reproduced library cone {rep['library_cone_constants']} != "
                    f"SPEC.md {spec_cone['libraries']}"
                )
        checks.append("alpoge_export_reproduction")

    # 9. Optional Lean source-tree reproduction
    if tree_specs:
        reproduced["trees"] = {}
        for eid, src_dir in tree_specs:
            if eid not in ed_index:
                errors.append(f"tree: unknown edition id {eid!r} (valid: {ed_ids})")
                continue
            measured = scan_lean_tree(src_dir)
            reproduced["trees"][eid] = measured
            for row_label, m_key in TREE_ROW_KEYS:
                expected = cell(row_label, eid)
                if expected is None:
                    continue
                if measured[m_key] != expected:
                    errors.append(
                        f"tree[{eid}]: editions.json {row_label!r}={expected!r} != reproduced {measured[m_key]!r}"
                    )
        checks.append("lean_tree_reproduction")

    return {
        "pass": len(errors) == 0,
        "editions_file": str(editions_path),
        "checks": checks,
        "errors": errors,
        "reproduced": reproduced,
    }


def _parse_tree_arg(raw: str) -> tuple[str, Path]:
    if "=" not in raw:
        raise argparse.ArgumentTypeError("expected EDITION_ID=PATH_TO_SRC")
    eid, path_str = raw.split("=", 1)
    eid = eid.strip()
    path_str = path_str.strip()
    if not eid or not path_str:
        raise argparse.ArgumentTypeError("expected non-empty EDITION_ID=PATH_TO_SRC")
    return eid, Path(path_str)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--editions", type=Path, default=REPO_ROOT / "docs" / "data" / "editions.json")
    parser.add_argument("--summary", type=Path, default=REPO_ROOT / "data" / "kernel_backbone_summary.json")
    parser.add_argument("--spec", type=Path, default=REPO_ROOT / "SPEC.md")
    parser.add_argument("--tracker", type=Path, default=REPO_ROOT / "docs" / "tracker.html")
    parser.add_argument(
        "--alpoge-export",
        type=Path,
        default=None,
        help="Optional directory with Alpoge v0.2.1 directories.csv.gz, decls.csv.gz, constants.csv.gz",
    )
    parser.add_argument(
        "--tree",
        action="append",
        type=_parse_tree_arg,
        default=[],
        metavar="EDITION_ID=SRC_DIR",
        help="Optional Lean src/ tree to reproduce static source metrics against editions.json (repeatable)",
    )
    parser.add_argument("--json-out", type=Path, default=None, help="Optional path to write JSON audit report")
    args = parser.parse_args(argv)

    try:
        result = audit_editions(
            editions_path=args.editions,
            summary_path=args.summary,
            spec_path=args.spec,
            tracker_path=args.tracker,
            alpoge_export_dir=args.alpoge_export,
            tree_specs=args.tree,
        )
    except (OSError, json.JSONDecodeError) as exc:
        print(f"[ERROR] {exc}", file=sys.stderr)
        return 2

    status = "PASS" if result["pass"] else "FAIL"
    print(f"[{status}] editions scope audit: checks={len(result['checks'])}, errors={len(result['errors'])}")
    for err in result["errors"]:
        print(f"  - {err}")

    if args.json_out is not None:
        args.json_out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())

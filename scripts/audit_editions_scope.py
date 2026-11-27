#!/usr/bin/env python3
"""Audit and reproduce the aggregation scopes in docs/data/editions.json.

Runs in two complementary modes with the Python standard library alone:

1. Standalone repository audit (default, no external data required):
   Cross-checks docs/data/editions.json against data/kernel_backbone_summary.json,
   SPEC.md, and docs/tracker.html to verify schema integrity, internal arithmetic,
   project-only vs. library-inclusive kernel-cone scope boundaries, and archive
   footnote coverage.

2. Ground-truth reproduction (optional flags):
   - --alpoge-export <dir>: reproduces the Alpoge v0.2.1 file, line, declaration,
     and per-origin kernel-constant counts directly from directories.csv(.gz),
     decls.csv(.gz), and constants.csv(.gz).
   - --tree <edition_id>=<src_dir> (repeatable): scans a Lean source tree with
     nested-comment stripping and reproduces all nine static source rows for that
     edition column.
   - --kernel-db <edition_id>=<sqlite_path> (repeatable): reads a read-only SQLite
     kernel index and reproduces kernel-constant and proof-cone rows for that
     edition column.

Usage:
    python scripts/audit_editions_scope.py
    python scripts/audit_editions_scope.py \
        --alpoge-export path/to/v0.2.1-kernel-export \
        --tree grh_readable=path/to/grh/src \
        --tree grh_compact=path/to/grh-compact/src
"""
from __future__ import annotations

import argparse
from collections import Counter
import csv
import gzip
import json
import math
from pathlib import Path
import re
import sqlite3
import sys
from typing import Any

EXPECTED_EDITION_IDS = (
    "alpoge_v021",
    "grh_readable",
    "grh_compact",
    "grh_clean",
)
VALID_FORMATS = {"int", "dec", "bytes", "dur"}
INT_FORMATS = {"int", "bytes", "dur"}
EXPECTED_ARCHIVE_ROWS = frozenset({"Files", "Raw lines", "Source size"})

TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|\d+|[^\sA-Za-z0-9_]")
SEMI_RE = re.compile(r";")

SPEC_ORIGIN_RE = re.compile(
    r"`(?P<full_cone>[0-9,]+)`\s+kernel constants\s+\(`cone-constants\.txt\.gz`\):\s+"
    r"`(?P<project>[0-9,]+)`\s+project,\s+"
    r"`(?P<mathlib>[0-9,]+)`\s+Mathlib,\s+"
    r"`(?P<core>[0-9,]+)`\s+Lean core,\s+"
    r"`(?P<batteries>[0-9,]+)`\s+Batteries,\s+"
    r"`(?P<aesop>[0-9,]+)`\s+Aesop"
)

TREE_ROW_MAP = (
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


def _parse_int_commas(text: str) -> int:
    return int(text.replace(",", ""))


def _is_valid_number(value: Any, fmt: str) -> bool:
    if isinstance(value, bool):
        return False
    if fmt in INT_FORMATS:
        return isinstance(value, int) and value >= 0
    return isinstance(value, (int, float)) and math.isfinite(value) and value >= 0


def _open_maybe_gz(path: Path):
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8", newline="")
    return path.open("rt", encoding="utf-8", newline="")


def _resolve_export_file(export_dir: Path, stem: str) -> Path:
    for name in (f"{stem}.csv.gz", f"{stem}.csv"):
        candidate = export_dir / name
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(
        f"Missing {stem}.csv.gz (or {stem}.csv) under {export_dir}"
    )


def strip_lean_comments(text: str) -> str:
    """Strip Lean 4 nested block comments (/- ... -/) and line comments (-- ...).

    String literals ("...") with backslash escapes are preserved so comment
    delimiters inside strings are not mistaken for comments.
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
    """Measure all static source-tree metrics for a directory of Lean files."""
    if not src_dir.is_dir():
        raise FileNotFoundError(f"Lean source directory not found: {src_dir}")

    tot: Counter[str] = Counter()
    max_line_len = 0
    for path in sorted(src_dir.rglob("*.lean")):
        raw = path.read_text(encoding="utf-8", errors="replace")
        raw_lines = raw.splitlines()
        code = strip_lean_comments(raw)
        code_lines_list = [ln for ln in code.splitlines() if ln.strip()]
        non_ws = sum(
            len(ln.replace(" ", "").replace("\t", "")) for ln in code_lines_list
        )
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
        "avg_non_ws_per_code_line": (
            round(tot["non_ws"] / code_lines, 2) if code_lines else 0.0
        ),
        "semis_per_1k_code_lines": (
            round(tot["semis"] * 1000.0 / code_lines, 2) if code_lines else 0.0
        ),
    }


def load_alpoge_export(export_dir: Path) -> dict[str, Any]:
    """Aggregate v0.2.1 Alpoge kernel-export CSVs by directory, decl, and origin."""
    dirs_path = _resolve_export_file(export_dir, "directories")
    decls_path = _resolve_export_file(export_dir, "decls")
    consts_path = _resolve_export_file(export_dir, "constants")

    top_dirs: list[str] = []
    dir_files = 0
    dir_files_in_cone = 0
    dir_raw_lines = 0
    dir_decls_total = 0
    dir_decls_in_cone = 0
    dir_lines_in_cone = 0
    with _open_maybe_gz(dirs_path) as f:
        for row in csv.DictReader(f):
            if row.get("level") == "1":
                top_dirs.append(row["dir"])
                dir_files += int(row["files"])
                if "files_in_cone" in row and row["files_in_cone"]:
                    dir_files_in_cone += int(row["files_in_cone"])
                dir_raw_lines += int(row["lines"])
                if "decls" in row and row["decls"]:
                    dir_decls_total += int(row["decls"])
                dir_decls_in_cone += int(row["decls_in_cone"])
                dir_lines_in_cone += int(row["lines_in_cone"])

    decls_total = 0
    decls_in_cone = 0
    decl_lines_in_cone = 0
    decl_origins: Counter[str] = Counter()
    with _open_maybe_gz(decls_path) as f:
        reader = csv.DictReader(f)
        has_origin = "origin" in (reader.fieldnames or [])
        for row in reader:
            decls_total += 1
            if has_origin:
                decl_origins[row["origin"]] += 1
            if row["in_cone"].lower() == "true":
                decls_in_cone += 1
                decl_lines_in_cone += int(row["lines"])

    consts_total = 0
    cone_by_origin: Counter[str] = Counter()
    with _open_maybe_gz(consts_path) as f:
        for row in csv.DictReader(f):
            consts_total += 1
            if row["in_cone"].lower() == "true":
                cone_by_origin[row["origin"]] += 1

    full_cone = sum(cone_by_origin.values())
    project_cone = cone_by_origin.get("project", 0)
    return {
        "top_dirs": top_dirs,
        "directories": {
            "files": dir_files,
            "files_in_cone": dir_files_in_cone,
            "raw_lines": dir_raw_lines,
            "decls_total": dir_decls_total,
            "decls_in_cone": dir_decls_in_cone,
            "lines_in_cone": dir_lines_in_cone,
        },
        "decls": {
            "total": decls_total,
            "in_cone": decls_in_cone,
            "lines_in_cone": decl_lines_in_cone,
            "origins": dict(decl_origins),
        },
        "constants": {
            "total_rows": consts_total,
            "full_cone": full_cone,
            "project_cone": project_cone,
            "library_cone": full_cone - project_cone,
            "by_origin": dict(cone_by_origin),
        },
    }


def load_kernel_db(db_path: Path) -> dict[str, int | None]:
    """Read kernel-constant and proof-cone counts from a read-only SQLite index."""
    resolved = db_path.resolve()
    if not resolved.is_file():
        raise FileNotFoundError(f"SQLite kernel index not found: {db_path}")
    uri = resolved.as_uri() + "?mode=ro"
    con = sqlite3.connect(uri, uri=True)
    try:
        cur = con.cursor()
        cols = {row[1] for row in cur.execute("PRAGMA table_info(decls)").fetchall()}
        if not cols:
            raise ValueError(f"SQLite database has no 'decls' table: {db_path}")
        total = cur.execute("SELECT COUNT(*) FROM decls").fetchone()[0]
        cone = (
            cur.execute("SELECT COUNT(*) FROM decls WHERE in_cone=1").fetchone()[0]
            if "in_cone" in cols
            else None
        )
        user_cone = (
            cur.execute(
                "SELECT COUNT(*) FROM decls WHERE is_internal=0 AND in_cone=1"
            ).fetchone()[0]
            if {"is_internal", "in_cone"} <= cols
            else None
        )
        return {
            "kernel_constants": int(total),
            "cone_constants": int(cone) if cone is not None else None,
            "user_cone_decls": int(user_cone) if user_cone is not None else None,
        }
    finally:
        con.close()


def parse_spec_origin_breakdown(spec_text: str) -> dict[str, int] | None:
    """Parse the Section 1 full-cone constant origin breakdown from SPEC.md."""
    m = SPEC_ORIGIN_RE.search(spec_text)
    if not m:
        return None
    full_cone = _parse_int_commas(m.group("full_cone"))
    project = _parse_int_commas(m.group("project"))
    mathlib = _parse_int_commas(m.group("mathlib"))
    core = _parse_int_commas(m.group("core"))
    batteries = _parse_int_commas(m.group("batteries"))
    aesop = _parse_int_commas(m.group("aesop"))
    return {
        "full_cone": full_cone,
        "project": project,
        "mathlib": mathlib,
        "core": core,
        "batteries": batteries,
        "aesop": aesop,
        "libraries": full_cone - project,
    }


def extract_edition_compare_block(tracker_html: str) -> str | None:
    """Extract the #edition-compare section and its inline rendering script."""
    start = tracker_html.find('id="edition-compare"')
    if start == -1:
        return None
    end = tracker_html.find("</script>", start)
    if end == -1:
        return None
    return tracker_html[start : end + len("</script>")]


def audit_editions(
    editions_data: dict[str, Any],
    summary_data: dict[str, Any] | None = None,
    spec_text: str | None = None,
    tracker_html: str | None = None,
    alpoge_export: dict[str, Any] | None = None,
    trees: dict[str, dict[str, int | float]] | None = None,
    kernel_dbs: dict[str, dict[str, int | None]] | None = None,
) -> dict[str, Any]:
    """Run all scope, unit, arithmetic, cross-file, and artifact audits."""
    errors: list[str] = []
    warnings: list[str] = []
    checks_passed = 0

    def check(cond: bool, msg: str) -> None:
        nonlocal checks_passed
        if cond:
            checks_passed += 1
        else:
            errors.append(msg)

    # 1. Schema and structural integrity
    check(editions_data.get("schema") == 1, f"schema must be 1, got {editions_data.get('schema')!r}")

    editions = editions_data.get("editions")
    check(
        isinstance(editions, list) and len(editions) > 0,
        "editions must be a non-empty list",
    )
    ed_ids: list[str] = []
    if isinstance(editions, list):
        for idx, entry in enumerate(editions):
            ok_entry = (
                isinstance(entry, dict)
                and isinstance(entry.get("id"), str)
                and bool(entry["id"].strip())
                and isinstance(entry.get("label"), str)
                and bool(entry["label"].strip())
            )
            check(ok_entry, f"editions[{idx}] must have non-empty string id and label")
            if ok_entry:
                ed_ids.append(entry["id"])
    check(len(ed_ids) == len(set(ed_ids)), f"duplicate edition ids: {ed_ids}")
    check(
        tuple(ed_ids) == EXPECTED_EDITION_IDS,
        f"edition ids must be {EXPECTED_EDITION_IDS}, got {tuple(ed_ids)}",
    )
    ed_idx = {eid: i for i, eid in enumerate(ed_ids)}

    rows_raw = editions_data.get("rows")
    check(
        isinstance(rows_raw, list) and len(rows_raw) > 0,
        "rows must be a non-empty list",
    )
    rows_by_label: dict[str, dict[str, Any]] = {}
    if isinstance(rows_raw, list):
        for idx, row in enumerate(rows_raw):
            label = row.get("label") if isinstance(row, dict) else None
            fmt = row.get("fmt") if isinstance(row, dict) else None
            values = row.get("values") if isinstance(row, dict) else None
            valid_row = (
                isinstance(label, str)
                and bool(label.strip())
                and fmt in VALID_FORMATS
                and isinstance(values, list)
                and len(values) == len(ed_ids)
            )
            check(
                valid_row,
                f"rows[{idx}] ({label!r}) must have valid label, fmt in {sorted(VALID_FORMATS)}, "
                f"and {len(ed_ids)} values",
            )
            if not valid_row:
                continue
            check(label not in rows_by_label, f"duplicate row label: {label!r}")
            rows_by_label[label] = row
            for eid, val in zip(ed_ids, values):
                if val is not None:
                    check(
                        _is_valid_number(val, fmt),
                        f"row {label!r} [{eid}] has invalid {fmt} value: {val!r}",
                    )

    def get_val(label: str, eid: str) -> int | float | None:
        row = rows_by_label.get(label)
        if row is None or eid not in ed_idx:
            return None
        vals = row.get("values")
        if not isinstance(vals, list) or ed_idx[eid] >= len(vals):
            return None
        return vals[ed_idx[eid]]

    # 2. Scope & unit boundary invariants (guards against historical mis-scopes)
    scope_text = editions_data.get("alpoge_archive_scope")
    check(
        isinstance(scope_text, str) and bool(scope_text.strip()),
        "alpoge_archive_scope must be a non-empty string",
    )
    if isinstance(scope_text, str):
        check(
            "175,187" in scope_text and "src/" in scope_text and "SPEC.md §1" in scope_text,
            "alpoge_archive_scope must document the 175,187 src/ files and cite SPEC.md §1",
        )
        check(
            "136,266" not in scope_text,
            "alpoge_archive_scope must not contain the retracted '136,266' Mathlib file claim",
        )
        check(
            "not part of the archive" in scope_text.lower()
            or "outside the archive" in scope_text.lower(),
            "alpoge_archive_scope must clarify that Mathlib was not part of the archive",
        )

    flagged_archive = frozenset(
        label
        for label, row in rows_by_label.items()
        if row.get("alpoge_archive") is True
    )
    check(
        flagged_archive == EXPECTED_ARCHIVE_ROWS,
        f"rows with alpoge_archive=true must be exactly {sorted(EXPECTED_ARCHIVE_ROWS)}, "
        f"got {sorted(flagged_archive)}",
    )
    for label, row in rows_by_label.items():
        if "alpoge_archive" in row:
            check(
                isinstance(row["alpoge_archive"], bool),
                f"row {label!r} alpoge_archive must be bool",
            )

    # Alpoge v0.2.1 line-unit separation: decl lines in cone != stripped code lines
    check(
        get_val("Code lines (no comments or blanks)", "alpoge_v021") is None,
        "alpoge_v021 'Code lines (no comments or blanks)' must be null "
        "(do not place proof-cone declaration lines into the comment-stripped code-lines row)",
    )
    alpoge_decl_lines = get_val("Declaration lines in the proof cone", "alpoge_v021")
    alpoge_raw_lines = get_val("Raw lines", "alpoge_v021")
    check(
        isinstance(alpoge_decl_lines, int) and alpoge_decl_lines > 0,
        "alpoge_v021 'Declaration lines in the proof cone' must be a positive int",
    )
    if isinstance(alpoge_decl_lines, int) and isinstance(alpoge_raw_lines, int):
        check(
            alpoge_decl_lines <= alpoge_raw_lines,
            f"alpoge_v021 declaration lines in cone ({alpoge_decl_lines}) exceed raw lines ({alpoge_raw_lines})",
        )

    # Monotonicity across every edition column
    for eid in ed_ids:
        raw_l = get_val("Raw lines", eid)
        code_l = get_val("Code lines (no comments or blanks)", eid)
        if isinstance(raw_l, int) and isinstance(code_l, int):
            check(
                0 < code_l <= raw_l,
                f"[{eid}] code lines ({code_l}) must satisfy 0 < code_lines <= raw_lines ({raw_l})",
            )

        k_const = get_val("Kernel constants", eid)
        cone_const = get_val("Constants in the proof cone", eid)
        cone_decl = get_val("Declarations in the proof cone", eid)
        if isinstance(k_const, int) and isinstance(cone_const, int):
            check(
                0 < cone_const <= k_const,
                f"[{eid}] Constants in the proof cone ({cone_const}) must satisfy <= Kernel constants ({k_const})",
            )
        if isinstance(cone_const, int) and isinstance(cone_decl, int):
            check(
                0 < cone_decl <= cone_const,
                f"[{eid}] Declarations in the proof cone ({cone_decl}) must satisfy <= Constants in the proof cone ({cone_const})",
            )
            if eid == "alpoge_v021":
                check(
                    cone_decl < cone_const,
                    f"[alpoge_v021] Constants in the proof cone ({cone_const}) must exceed "
                    f"Declarations in the proof cone ({cone_decl}) because Lean generates auxiliary constants",
                )

        # Derived ratio consistency: non_ws / code_lines
        non_ws = get_val("Non-whitespace code characters", eid)
        avg_nws = get_val("Non-whitespace characters per code line", eid)
        if (
            isinstance(code_l, int)
            and code_l > 0
            and isinstance(non_ws, int)
            and isinstance(avg_nws, (int, float))
        ):
            expected_avg = round(non_ws / code_l, 2)
            check(
                abs(expected_avg - float(avg_nws)) <= 1e-9,
                f"[{eid}] Non-whitespace characters per code line is {avg_nws}, "
                f"expected round({non_ws} / {code_l}, 2) = {expected_avg}",
            )

    # 3. export_inversion cross-checks
    inv = editions_data.get("export_inversion")
    check(isinstance(inv, dict), "export_inversion must be an object")
    if isinstance(inv, dict):
        r_exp = get_val("Kernel export size", "grh_readable")
        c_exp = get_val("Kernel export size", "grh_compact")
        r_bld = get_val("Cold build time", "grh_readable")
        c_bld = get_val("Cold build time", "grh_compact")
        r_cl = get_val("Code lines (no comments or blanks)", "grh_readable")
        c_cl = get_val("Code lines (no comments or blanks)", "grh_compact")

        check(
            inv.get("readable_export_bytes") == r_exp,
            f"export_inversion.readable_export_bytes ({inv.get('readable_export_bytes')}) != table ({r_exp})",
        )
        check(
            inv.get("compact_export_bytes") == c_exp,
            f"export_inversion.compact_export_bytes ({inv.get('compact_export_bytes')}) != table ({c_exp})",
        )
        check(
            inv.get("readable_build_sec") == r_bld,
            f"export_inversion.readable_build_sec ({inv.get('readable_build_sec')}) != table ({r_bld})",
        )
        check(
            inv.get("compact_build_sec") == c_bld,
            f"export_inversion.compact_build_sec ({inv.get('compact_build_sec')}) != table ({c_bld})",
        )
        if isinstance(r_exp, int) and r_exp > 0 and isinstance(c_exp, int):
            exp_pct = round((c_exp - r_exp) * 100.0 / r_exp, 1)
            check(
                inv.get("compact_vs_readable_export_pct") == exp_pct,
                f"export_inversion.compact_vs_readable_export_pct ({inv.get('compact_vs_readable_export_pct')}) "
                f"!= computed {exp_pct}",
            )
        if isinstance(r_cl, int) and r_cl > 0 and isinstance(c_cl, int):
            cl_pct = round((c_cl - r_cl) * 100.0 / r_cl, 1)
            check(
                inv.get("compact_vs_readable_code_lines_pct") == cl_pct,
                f"export_inversion.compact_vs_readable_code_lines_pct "
                f"({inv.get('compact_vs_readable_code_lines_pct')}) != computed {cl_pct}",
            )

    # 4. cross_repo_pairing arithmetic consistency
    pair = editions_data.get("cross_repo_pairing")
    check(isinstance(pair, dict), "cross_repo_pairing must be an object")
    if isinstance(pair, dict):
        grh_files = get_val("Files", "grh_readable")
        cmp_files = get_val("Files", "grh_compact")
        check(
            pair.get("grh_modules") == grh_files,
            f"cross_repo_pairing.grh_modules ({pair.get('grh_modules')}) != Files[grh_readable] ({grh_files})",
        )
        check(
            pair.get("compact_modules") == cmp_files,
            f"cross_repo_pairing.compact_modules ({pair.get('compact_modules')}) != Files[grh_compact] ({cmp_files})",
        )
        common = pair.get("common_path_modules")
        g_only = pair.get("grh_only_total")
        c_only = pair.get("compact_only_total")
        if all(isinstance(v, int) for v in (common, g_only, pair.get("grh_modules"))):
            check(
                common + g_only == pair["grh_modules"],
                f"common_path_modules ({common}) + grh_only_total ({g_only}) != grh_modules ({pair['grh_modules']})",
            )
        if all(isinstance(v, int) for v in (common, c_only, pair.get("compact_modules"))):
            check(
                common + c_only == pair["compact_modules"],
                f"common_path_modules ({common}) + compact_only_total ({c_only}) != compact_modules ({pair['compact_modules']})",
            )
        accepted = pair.get("non_identical_pairs_accepted")
        g_cov = pair.get("grh_only_covered")
        c_cov = pair.get("compact_only_covered")
        if all(isinstance(v, int) for v in (accepted, g_cov, g_only)):
            check(
                0 <= accepted <= g_cov <= g_only,
                f"invalid grh_only coverage chain: accepted={accepted}, covered={g_cov}, total={g_only}",
            )
        if all(isinstance(v, int) for v in (accepted, c_cov, c_only)):
            check(
                0 <= accepted <= c_cov <= c_only,
                f"invalid compact_only coverage chain: accepted={accepted}, covered={c_cov}, total={c_only}",
            )
        hc_pairs = pair.get("high_confidence_pairs")
        hc_short = pair.get("high_confidence_genuine_shorter")
        hc_1to1 = pair.get("high_confidence_1to1_genuine_shorter")
        if all(isinstance(v, int) for v in (hc_1to1, hc_short, hc_pairs, accepted)):
            check(
                0 <= hc_1to1 <= hc_short <= hc_pairs <= accepted,
                f"invalid high-confidence chain: 1to1={hc_1to1}, shorter={hc_short}, "
                f"hc_pairs={hc_pairs}, accepted={accepted}",
            )
        saved_all = pair.get("high_confidence_genuine_shorter_non_ws_saved")
        saved_1to1 = pair.get("high_confidence_1to1_non_ws_saved")
        if isinstance(saved_all, int) and isinstance(saved_1to1, int):
            check(
                0 <= saved_1to1 <= saved_all,
                f"1to1 saved ({saved_1to1}) must be <= total genuine-shorter saved ({saved_all})",
            )
        ref_tot = pair.get("references_total")
        ref_unp = pair.get("references_unplaced")
        ref_hi = pair.get("references_unplaced_high")
        ref_md = pair.get("references_unplaced_medium")
        ref_lo = pair.get("references_unplaced_low")
        if all(isinstance(v, int) for v in (ref_tot, ref_unp, ref_hi, ref_md, ref_lo)):
            check(
                ref_hi + ref_md + ref_lo == ref_unp <= ref_tot,
                f"references_unplaced breakdown ({ref_hi}+{ref_md}+{ref_lo}) != {ref_unp} (total {ref_tot})",
            )
        tc_all = pair.get("tauceti_candidates")
        tc_thm = pair.get("tauceti_candidate_theorems")
        if isinstance(tc_all, int) and isinstance(tc_thm, int):
            check(
                0 <= tc_thm <= tc_all,
                f"tauceti_candidate_theorems ({tc_thm}) must be <= tauceti_candidates ({tc_all})",
            )

    # 5. Cross-check against data/kernel_backbone_summary.json
    if summary_data is not None:
        gt = summary_data.get("global_totals", {})
        check(
            gt.get("files_total") == get_val("Files", "alpoge_v021"),
            f"summary global_totals.files_total ({gt.get('files_total')}) != "
            f"editions Files[alpoge_v021] ({get_val('Files', 'alpoge_v021')})",
        )
        check(
            gt.get("raw_source_lines_total") == get_val("Raw lines", "alpoge_v021"),
            f"summary global_totals.raw_source_lines_total ({gt.get('raw_source_lines_total')}) != "
            f"editions Raw lines[alpoge_v021] ({get_val('Raw lines', 'alpoge_v021')})",
        )
        check(
            gt.get("decl_lines_in_cone")
            == get_val("Declaration lines in the proof cone", "alpoge_v021"),
            f"summary global_totals.decl_lines_in_cone ({gt.get('decl_lines_in_cone')}) != "
            f"editions Declaration lines in the proof cone[alpoge_v021] "
            f"({get_val('Declaration lines in the proof cone', 'alpoge_v021')})",
        )
        check(
            gt.get("decls_in_cone")
            == get_val("Declarations in the proof cone", "alpoge_v021"),
            f"summary global_totals.decls_in_cone ({gt.get('decls_in_cone')}) != "
            f"editions Declarations in the proof cone[alpoge_v021] "
            f"({get_val('Declarations in the proof cone', 'alpoge_v021')})",
        )
        tld = summary_data.get("top_level_directories", [])
        check(
            isinstance(tld, list) and len(tld) > 0,
            "summary top_level_directories must be a non-empty list",
        )
        if isinstance(tld, list) and tld:
            non_src = [d.get("dir") for d in tld if not str(d.get("dir", "")).startswith("src/")]
            check(
                not non_src,
                f"summary top_level_directories contains non-src entries: {non_src}",
            )
            check(
                sum(int(d["files"]) for d in tld) == gt.get("files_total"),
                "sum of top_level_directories.files != global_totals.files_total",
            )
            check(
                sum(int(d["raw_lines"]) for d in tld) == gt.get("raw_source_lines_total"),
                "sum of top_level_directories.raw_lines != global_totals.raw_source_lines_total",
            )
            check(
                sum(int(d["decls_in_cone"]) for d in tld) == gt.get("decls_in_cone"),
                "sum of top_level_directories.decls_in_cone != global_totals.decls_in_cone",
            )
            check(
                sum(int(d["lines_in_cone"]) for d in tld) == gt.get("decl_lines_in_cone"),
                "sum of top_level_directories.lines_in_cone != global_totals.decl_lines_in_cone",
            )

    # 6. Cross-check against SPEC.md Section 1 origin breakdown
    spec_origins: dict[str, int] | None = None
    if spec_text is not None:
        spec_origins = parse_spec_origin_breakdown(spec_text)
        check(
            spec_origins is not None,
            "could not parse Section 1 kernel-constant origin breakdown from SPEC.md",
        )
        if spec_origins is not None:
            origin_sum = (
                spec_origins["project"]
                + spec_origins["mathlib"]
                + spec_origins["core"]
                + spec_origins["batteries"]
                + spec_origins["aesop"]
            )
            check(
                origin_sum == spec_origins["full_cone"],
                f"SPEC.md origin parts sum to {origin_sum}, expected {spec_origins['full_cone']}",
            )
            alpoge_cone_const = get_val("Constants in the proof cone", "alpoge_v021")
            check(
                alpoge_cone_const == spec_origins["project"],
                f"editions Constants in the proof cone[alpoge_v021] ({alpoge_cone_const}) must match "
                f"SPEC.md project-only constant count ({spec_origins['project']}), not full cone "
                f"({spec_origins['full_cone']})",
            )

    # 7. Cross-check against docs/tracker.html #edition-compare explanation
    if tracker_html is not None:
        block = extract_edition_compare_block(tracker_html)
        check(
            block is not None,
            "could not locate id=\"edition-compare\" section and script in docs/tracker.html",
        )
        if block is not None:
            check(
                "alpoge_archive_scope" in block and "alpoge_archive" in block,
                "docs/tracker.html #edition-compare must render alpoge_archive_scope and alpoge_archive flags",
            )
            check(
                "136,266" not in block,
                "docs/tracker.html #edition-compare must not contain the retracted '136,266' claim",
            )
            if spec_origins is not None:
                full_fmt = f"{spec_origins['full_cone']:,}"
                libs_fmt = f"{spec_origins['libraries']:,}"
                check(
                    full_fmt in block and libs_fmt in block,
                    f"docs/tracker.html #edition-compare note must cite full cone ({full_fmt}) "
                    f"and excluded library subtotal ({libs_fmt})",
                )

    reproduced: dict[str, Any] = {}

    # 8. Optional ground-truth reproduction from Alpoge v0.2.1 kernel export
    if alpoge_export is not None:
        top_dirs = alpoge_export["top_dirs"]
        check(
            bool(top_dirs) and all(d.startswith("src/") for d in top_dirs),
            f"Alpoge directories.csv level-1 entries must all start with 'src/', got {top_dirs}",
        )
        d_agg = alpoge_export["directories"]
        check(
            d_agg["files"] == get_val("Files", "alpoge_v021"),
            f"directories.csv files ({d_agg['files']}) != editions Files[alpoge_v021] ({get_val('Files', 'alpoge_v021')})",
        )
        check(
            d_agg["raw_lines"] == get_val("Raw lines", "alpoge_v021"),
            f"directories.csv raw lines ({d_agg['raw_lines']}) != editions Raw lines[alpoge_v021] ({get_val('Raw lines', 'alpoge_v021')})",
        )
        check(
            d_agg["decls_in_cone"] == get_val("Declarations in the proof cone", "alpoge_v021"),
            f"directories.csv decls_in_cone ({d_agg['decls_in_cone']}) != "
            f"editions Declarations in the proof cone[alpoge_v021] ({get_val('Declarations in the proof cone', 'alpoge_v021')})",
        )
        check(
            d_agg["lines_in_cone"] == get_val("Declaration lines in the proof cone", "alpoge_v021"),
            f"directories.csv lines_in_cone ({d_agg['lines_in_cone']}) != "
            f"editions Declaration lines in the proof cone[alpoge_v021] "
            f"({get_val('Declaration lines in the proof cone', 'alpoge_v021')})",
        )

        dec_agg = alpoge_export["decls"]
        check(
            dec_agg["in_cone"] == get_val("Declarations in the proof cone", "alpoge_v021"),
            f"decls.csv in_cone ({dec_agg['in_cone']}) != "
            f"editions Declarations in the proof cone[alpoge_v021] ({get_val('Declarations in the proof cone', 'alpoge_v021')})",
        )
        check(
            dec_agg["lines_in_cone"] == get_val("Declaration lines in the proof cone", "alpoge_v021"),
            f"decls.csv in_cone lines ({dec_agg['lines_in_cone']}) != "
            f"editions Declaration lines in the proof cone[alpoge_v021] "
            f"({get_val('Declaration lines in the proof cone', 'alpoge_v021')})",
        )
        if dec_agg["origins"]:
            check(
                set(dec_agg["origins"].keys()) == {"project"},
                f"decls.csv origins must be project-only, got {dec_agg['origins']}",
            )

        c_agg = alpoge_export["constants"]
        check(
            c_agg["project_cone"] == get_val("Constants in the proof cone", "alpoge_v021"),
            f"constants.csv project in_cone ({c_agg['project_cone']}) != "
            f"editions Constants in the proof cone[alpoge_v021] ({get_val('Constants in the proof cone', 'alpoge_v021')})",
        )
        if spec_origins is not None:
            check(
                c_agg["full_cone"] == spec_origins["full_cone"],
                f"constants.csv full cone ({c_agg['full_cone']}) != SPEC.md ({spec_origins['full_cone']})",
            )
            check(
                c_agg["library_cone"] == spec_origins["libraries"],
                f"constants.csv library cone ({c_agg['library_cone']}) != SPEC.md ({spec_origins['libraries']})",
            )
            for origin_key in ("project", "mathlib", "core", "batteries", "aesop"):
                got_origin = c_agg["by_origin"].get(origin_key, 0)
                check(
                    got_origin == spec_origins[origin_key],
                    f"constants.csv origin={origin_key!r} ({got_origin}) != SPEC.md ({spec_origins[origin_key]})",
                )
        reproduced["alpoge_export"] = alpoge_export

    # 9. Optional ground-truth reproduction from Lean source trees
    if trees:
        reproduced["trees"] = {}
        for eid, metrics in trees.items():
            check(eid in ed_idx, f"--tree references unknown edition id: {eid!r}")
            if eid not in ed_idx:
                continue
            for row_label, metric_key in TREE_ROW_MAP:
                expected = get_val(row_label, eid)
                actual = metrics[metric_key]
                check(
                    expected is not None,
                    f"--tree [{eid}] cannot compare row {row_label!r} because editions.json value is null",
                )
                if expected is not None:
                    matches = (
                        abs(float(actual) - float(expected)) <= 1e-9
                        if isinstance(expected, float) or isinstance(actual, float)
                        else actual == expected
                    )
                    check(
                        matches,
                        f"--tree [{eid}] {row_label!r}: measured {actual!r} != editions.json {expected!r}",
                    )
            reproduced["trees"][eid] = metrics

    # 10. Optional ground-truth reproduction from SQLite kernel indices
    if kernel_dbs:
        reproduced["kernel_dbs"] = {}
        for eid, db_metrics in kernel_dbs.items():
            check(eid in ed_idx, f"--kernel-db references unknown edition id: {eid!r}")
            if eid not in ed_idx:
                continue
            expected_total = get_val("Kernel constants", eid)
            if expected_total is not None:
                check(
                    db_metrics["kernel_constants"] == expected_total,
                    f"--kernel-db [{eid}] Kernel constants: measured {db_metrics['kernel_constants']} "
                    f"!= editions.json {expected_total}",
                )
            expected_cone = get_val("Constants in the proof cone", eid)
            if expected_cone is not None and db_metrics["cone_constants"] is not None:
                check(
                    db_metrics["cone_constants"] == expected_cone,
                    f"--kernel-db [{eid}] Constants in the proof cone: measured {db_metrics['cone_constants']} "
                    f"!= editions.json {expected_cone}",
                )
            expected_user = get_val("Declarations in the proof cone", eid)
            if expected_user is not None and db_metrics["user_cone_decls"] is not None:
                check(
                    db_metrics["user_cone_decls"] == expected_user,
                    f"--kernel-db [{eid}] Declarations in the proof cone: measured {db_metrics['user_cone_decls']} "
                    f"!= editions.json {expected_user}",
                )
            reproduced["kernel_dbs"][eid] = db_metrics

    return {
        "ok": len(errors) == 0,
        "checks_passed": checks_passed,
        "errors": errors,
        "warnings": warnings,
        "reproduced": reproduced,
    }


def _parse_edition_path_arg(raw: str, flag: str) -> tuple[str, Path]:
    if "=" not in raw:
        raise ValueError(f"{flag} expects <edition_id>=<path>, got {raw!r}")
    eid, path_str = raw.split("=", 1)
    eid = eid.strip()
    path_str = path_str.strip()
    if not eid or not path_str:
        raise ValueError(f"{flag} expects non-empty <edition_id>=<path>, got {raw!r}")
    return eid, Path(path_str)


def main(argv: list[str] | None = None) -> int:
    repo_root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(
        description="Audit and reproduce aggregation scopes in docs/data/editions.json."
    )
    parser.add_argument(
        "--editions",
        type=Path,
        default=repo_root / "docs" / "data" / "editions.json",
        help="Path to editions.json (default: docs/data/editions.json)",
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=repo_root / "data" / "kernel_backbone_summary.json",
        help="Path to kernel_backbone_summary.json (default: data/kernel_backbone_summary.json)",
    )
    parser.add_argument(
        "--spec",
        type=Path,
        default=repo_root / "SPEC.md",
        help="Path to SPEC.md (default: SPEC.md)",
    )
    parser.add_argument(
        "--tracker",
        type=Path,
        default=repo_root / "docs" / "tracker.html",
        help="Path to docs/tracker.html (default: docs/tracker.html)",
    )
    parser.add_argument(
        "--alpoge-export",
        type=Path,
        default=None,
        help="Optional directory holding v0.2.1 directories.csv.gz, decls.csv.gz, constants.csv.gz",
    )
    parser.add_argument(
        "--tree",
        action="append",
        default=[],
        metavar="EDITION_ID=SRC_DIR",
        help="Optional Lean src directory to scan and compare against an edition column (repeatable)",
    )
    parser.add_argument(
        "--kernel-db",
        action="append",
        default=[],
        metavar="EDITION_ID=SQLITE_PATH",
        help="Optional SQLite kernel index to compare against an edition column (repeatable)",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Optional path to write the JSON audit report",
    )
    args = parser.parse_args(argv)

    try:
        editions_data = json.loads(args.editions.read_text(encoding="utf-8"))
        summary_data = (
            json.loads(args.summary.read_text(encoding="utf-8"))
            if args.summary and args.summary.is_file()
            else None
        )
        spec_text = (
            args.spec.read_text(encoding="utf-8")
            if args.spec and args.spec.is_file()
            else None
        )
        tracker_html = (
            args.tracker.read_text(encoding="utf-8")
            if args.tracker and args.tracker.is_file()
            else None
        )

        alpoge_export = (
            load_alpoge_export(args.alpoge_export) if args.alpoge_export else None
        )
        trees: dict[str, dict[str, int | float]] = {}
        for item in args.tree:
            eid, src_dir = _parse_edition_path_arg(item, "--tree")
            trees[eid] = scan_lean_tree(src_dir)

        kernel_dbs: dict[str, dict[str, int | None]] = {}
        for item in args.kernel_db:
            eid, db_path = _parse_edition_path_arg(item, "--kernel-db")
            kernel_dbs[eid] = load_kernel_db(db_path)
    except (OSError, ValueError, sqlite3.Error) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    report = audit_editions(
        editions_data=editions_data,
        summary_data=summary_data,
        spec_text=spec_text,
        tracker_html=tracker_html,
        alpoge_export=alpoge_export,
        trees=trees or None,
        kernel_dbs=kernel_dbs or None,
    )

    if args.json_out:
        try:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(
                json.dumps(report, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        except OSError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 2

    status = "PASS" if report["ok"] else "FAIL"
    modes = ["repo"]
    if alpoge_export is not None:
        modes.append("alpoge-export")
    if trees:
        modes.append("trees:" + ",".join(sorted(trees)))
    if kernel_dbs:
        modes.append("kernel-dbs:" + ",".join(sorted(kernel_dbs)))
    print(
        f"[{status}] editions scope audit ({'+'.join(modes)}): "
        f"checks_passed={report['checks_passed']} errors={len(report['errors'])}"
    )
    for err in report["errors"]:
        print(f"  ERROR: {err}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

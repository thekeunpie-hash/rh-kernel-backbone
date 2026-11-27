#!/usr/bin/env python3
"""Unit tests for scripts/audit_editions_scope.py."""
from __future__ import annotations

import copy
import contextlib
import gzip
import io
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import audit_editions_scope as aes  # noqa: E402


def _load_live_inputs() -> tuple[dict, dict, str, str]:
    editions = json.loads(
        (REPO_ROOT / "docs" / "data" / "editions.json").read_text(encoding="utf-8")
    )
    summary = json.loads(
        (REPO_ROOT / "data" / "kernel_backbone_summary.json").read_text(encoding="utf-8")
    )
    spec = (REPO_ROOT / "SPEC.md").read_text(encoding="utf-8")
    tracker = (REPO_ROOT / "docs" / "tracker.html").read_text(encoding="utf-8")
    return editions, summary, spec, tracker


def _row_by_label(editions: dict, label: str) -> dict:
    for row in editions["rows"]:
        if row["label"] == label:
            return row
    raise KeyError(label)


class TestAuditEditionsScope(unittest.TestCase):
    def test_live_repo_passes(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        report = aes.audit_editions(
            editions_data=editions,
            summary_data=summary,
            spec_text=spec,
            tracker_html=tracker,
        )
        self.assertTrue(report["ok"], report["errors"])
        self.assertGreater(report["checks_passed"], 70)
        self.assertEqual(report["errors"], [])

    def test_rejects_decl_lines_in_code_lines_row(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut = copy.deepcopy(editions)
        _row_by_label(mut, "Code lines (no comments or blanks)")["values"][0] = 10737728
        report = aes.audit_editions(mut, summary, spec, tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("Code lines (no comments or blanks)" in e for e in report["errors"]),
            report["errors"],
        )

    def test_rejects_full_cone_library_constants_in_alpoge_column(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut = copy.deepcopy(editions)
        _row_by_label(mut, "Constants in the proof cone")["values"][0] = 1484729
        report = aes.audit_editions(mut, summary, spec, tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("project-only constant count" in e for e in report["errors"]),
            report["errors"],
        )

    def test_rejects_declarations_labeled_as_constants(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut = copy.deepcopy(editions)
        _row_by_label(mut, "Constants in the proof cone")["values"][0] = 804912
        report = aes.audit_editions(mut, summary, spec, tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("must exceed Declarations in the proof cone" in e for e in report["errors"]),
            report["errors"],
        )

    def test_rejects_retracted_mathlib_archive_claim(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut = copy.deepcopy(editions)
        mut["alpoge_archive_scope"] = (
            "175,187 files under src/ plus 136,266 Mathlib files (SPEC.md §1)."
        )
        report = aes.audit_editions(mut, summary, spec, tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(any("136,266" in e for e in report["errors"]), report["errors"])

    def test_rejects_missing_alpoge_archive_flag(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut = copy.deepcopy(editions)
        _row_by_label(mut, "Source size").pop("alpoge_archive")
        report = aes.audit_editions(mut, summary, spec, tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("alpoge_archive=true" in e for e in report["errors"]),
            report["errors"],
        )

    def test_rejects_derived_ratio_and_inversion_drift(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut = copy.deepcopy(editions)
        _row_by_label(mut, "Non-whitespace characters per code line")["values"][1] = 47.00
        mut["export_inversion"]["compact_vs_readable_export_pct"] = 14.0
        mut["cross_repo_pairing"]["grh_only_total"] = 728
        report = aes.audit_editions(mut, summary, spec, tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("Non-whitespace characters per code line" in e for e in report["errors"])
        )
        self.assertTrue(
            any("compact_vs_readable_export_pct" in e for e in report["errors"])
        )
        self.assertTrue(
            any("common_path_modules" in e for e in report["errors"])
        )

    def test_rejects_tracker_library_note_drift(self) -> None:
        editions, summary, spec, tracker = _load_live_inputs()
        mut_tracker = tracker.replace("214,545", "999,999")
        report = aes.audit_editions(editions, summary, spec, mut_tracker)
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("excluded library subtotal" in e for e in report["errors"]),
            report["errors"],
        )

    def test_strip_lean_comments_handles_nesting_and_strings(self) -> None:
        sample = (
            'def s := "-- not comment /- neither -/" -- real line comment\n'
            '/- outer /- nested -/ still outer -/\n'
            'theorem t : True := by trivial; -- trailing\n'
        )
        stripped = aes.strip_lean_comments(sample)
        self.assertIn('"-- not comment /- neither -/"', stripped)
        self.assertNotIn("real line comment", stripped)
        self.assertNotIn("nested", stripped)
        self.assertNotIn("trailing", stripped)
        self.assertIn("theorem t : True := by trivial;", stripped)

    def test_synthetic_tree_and_kernel_db_reproduction(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            src = root / "src"
            src.mkdir()
            (src / "A.lean").write_text(
                "-- header comment\n"
                "def alpha := 1; -- ok\n"
                "/- block\n"
                "  /- inner -/\n"
                "-/\n"
                'def beta := "x--y"\n',
                encoding="utf-8",
            )
            (src / "Sub").mkdir()
            (src / "Sub" / "B.lean").write_text(
                "theorem gamma : True := by\n"
                "  trivial; trivial\n",
                encoding="utf-8",
            )

            measured = aes.scan_lean_tree(src)
            self.assertEqual(measured["files"], 2)
            self.assertEqual(measured["raw_lines"], 8)
            self.assertEqual(measured["code_lines"], 4)
            self.assertEqual(measured["semis"], 2)
            self.assertEqual(measured["semis_per_1k_code_lines"], 500.0)

            db_path = root / "index.sqlite"
            con = sqlite3.connect(db_path)
            con.execute(
                "CREATE TABLE decls (name TEXT, in_cone INTEGER, is_internal INTEGER)"
            )
            con.executemany(
                "INSERT INTO decls VALUES (?, ?, ?)",
                [
                    ("a", 1, 0),
                    ("a._aux", 1, 1),
                    ("b", 1, 0),
                    ("dead", 0, 0),
                ],
            )
            con.commit()
            con.close()

            db_metrics = aes.load_kernel_db(db_path)
            self.assertEqual(
                db_metrics,
                {"kernel_constants": 4, "cone_constants": 3, "user_cone_decls": 2},
            )

            editions, _, _, _ = _load_live_inputs()
            mut = copy.deepcopy(editions)
            for label, key in aes.TREE_ROW_MAP:
                _row_by_label(mut, label)["values"][1] = measured[key]
            _row_by_label(mut, "Kernel constants")["values"][1] = 4
            _row_by_label(mut, "Constants in the proof cone")["values"][1] = 3
            _row_by_label(mut, "Declarations in the proof cone")["values"][1] = 2
            mut["cross_repo_pairing"]["grh_modules"] = 2
            mut["cross_repo_pairing"]["common_path_modules"] = 2
            mut["cross_repo_pairing"]["grh_only_total"] = 0
            mut["cross_repo_pairing"]["grh_only_covered"] = 0
            mut["cross_repo_pairing"]["non_identical_pairs_accepted"] = 0
            mut["cross_repo_pairing"]["high_confidence_pairs"] = 0
            mut["cross_repo_pairing"]["high_confidence_genuine_shorter"] = 0
            mut["cross_repo_pairing"]["high_confidence_1to1_genuine_shorter"] = 0
            mut["cross_repo_pairing"]["compact_modules"] = 794
            mut["cross_repo_pairing"]["compact_only_total"] = 792
            mut["cross_repo_pairing"]["compact_only_covered"] = 792
            c_cl = _row_by_label(mut, "Code lines (no comments or blanks)")["values"][2]
            mut["export_inversion"]["compact_vs_readable_code_lines_pct"] = round(
                (c_cl - measured["code_lines"]) * 100.0 / measured["code_lines"], 1
            )

            report = aes.audit_editions(
                editions_data=mut,
                trees={"grh_readable": measured},
                kernel_dbs={"grh_readable": db_metrics},
            )
            self.assertTrue(report["ok"], report["errors"])

            # Mutating one tree value must fail reproduction
            bad_tree = dict(measured)
            bad_tree["tokens"] = int(bad_tree["tokens"]) + 1
            bad_report = aes.audit_editions(
                editions_data=mut,
                trees={"grh_readable": bad_tree},
            )
            self.assertFalse(bad_report["ok"])
            self.assertTrue(any("Lean tokens" in e for e in bad_report["errors"]))

    def test_synthetic_alpoge_export_reproduction(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            exp = Path(tmp)
            with gzip.open(exp / "directories.csv.gz", "wt", encoding="utf-8", newline="") as f:
                f.write("level,dir,files,files_in_cone,lines,decls,decls_in_cone,lines_in_cone\n")
                f.write("0,src,10,8,500,20,15,300\n")
                f.write("1,src/Development,7,6,350,14,11,220\n")
                f.write("1,src/Formalism,3,2,150,6,4,80\n")
            with gzip.open(exp / "decls.csv.gz", "wt", encoding="utf-8", newline="") as f:
                f.write("decl,origin,in_cone,lines\n")
                for i in range(15):
                    f.write(f"Proj.d{i},project,true,20\n")
                for i in range(5):
                    f.write(f"Proj.dead{i},project,false,10\n")
            with gzip.open(exp / "constants.csv.gz", "wt", encoding="utf-8", newline="") as f:
                f.write("const,origin,in_cone\n")
                for i in range(25):
                    f.write(f"Proj.c{i},project,true\n")
                for i in range(6):
                    f.write(f"Mathlib.c{i},mathlib,true\n")
                f.write("Core.c0,core,true\n")
                f.write("Batteries.c0,batteries,true\n")
                f.write("Aesop.c0,aesop,true\n")
                f.write("Core.dead,core,false\n")

            loaded = aes.load_alpoge_export(exp)
            self.assertEqual(loaded["top_dirs"], ["src/Development", "src/Formalism"])
            self.assertEqual(loaded["constants"]["project_cone"], 25)
            self.assertEqual(loaded["constants"]["full_cone"], 34)
            self.assertEqual(loaded["constants"]["library_cone"], 9)

            editions, _, _, _ = _load_live_inputs()
            mut = copy.deepcopy(editions)
            _row_by_label(mut, "Files")["values"][0] = 10
            _row_by_label(mut, "Raw lines")["values"][0] = 500
            _row_by_label(mut, "Declaration lines in the proof cone")["values"][0] = 300
            _row_by_label(mut, "Declarations in the proof cone")["values"][0] = 15
            _row_by_label(mut, "Constants in the proof cone")["values"][0] = 25

            fake_spec = (
                "`34` kernel constants (`cone-constants.txt.gz`): "
                "`25` project, `6` Mathlib, `1` Lean core, `1` Batteries, `1` Aesop"
            )
            report = aes.audit_editions(
                editions_data=mut,
                spec_text=fake_spec,
                alpoge_export=loaded,
            )
            self.assertTrue(report["ok"], report["errors"])

            # Non-src level-1 directory must fail
            bad_export = copy.deepcopy(loaded)
            bad_export["top_dirs"].append("mathlib/Algebra")
            bad_report = aes.audit_editions(
                editions_data=mut,
                spec_text=fake_spec,
                alpoge_export=bad_export,
            )
            self.assertFalse(bad_report["ok"])
            self.assertTrue(
                any("must all start with 'src/'" in e for e in bad_report["errors"])
            )

    def test_cli_exit_codes_and_json_out(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            missing_editions = root / "does-not-exist.json"
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rc = aes.main(["--editions", str(missing_editions)])
            self.assertEqual(rc, 2)
            self.assertIn("ERROR:", err.getvalue())

            missing_tree = root / "missing-src"
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rc = aes.main(["--tree", f"grh_readable={missing_tree}"])
            self.assertEqual(rc, 2)
            self.assertIn("ERROR:", err.getvalue())

            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rc = aes.main(["--tree", "malformed-arg"])
            self.assertEqual(rc, 2)
            self.assertIn("ERROR:", err.getvalue())

            missing_db = root / "missing.sqlite"
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rc = aes.main(["--kernel-db", f"grh_readable={missing_db}"])
            self.assertEqual(rc, 2)
            self.assertIn("ERROR:", err.getvalue())

            # Audit failure remains exit 1 (distinct from CLI/input error exit 2).
            editions, _, _, _ = _load_live_inputs()
            mut = copy.deepcopy(editions)
            _row_by_label(mut, "Code lines (no comments or blanks)")["values"][0] = 10737728
            bad_editions = root / "bad-editions.json"
            bad_editions.write_text(json.dumps(mut), encoding="utf-8")
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = aes.main(["--editions", str(bad_editions)])
            self.assertEqual(rc, 1)
            self.assertIn("[FAIL]", out.getvalue())

            # --json-out writes a parseable passing report and returns 0.
            json_out = root / "nested" / "audit-report.json"
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = aes.main(["--json-out", str(json_out)])
            self.assertEqual(rc, 0, err.getvalue())
            self.assertTrue(json_out.is_file())
            written = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertTrue(written["ok"])
            self.assertGreater(written["checks_passed"], 70)
            self.assertEqual(written["errors"], [])


if __name__ == "__main__":
    unittest.main()

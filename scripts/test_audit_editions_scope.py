"""Tests for scripts/audit_editions_scope.py (stdlib only, no external downloads)."""
from __future__ import annotations

import copy
import csv
import gzip
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import audit_editions_scope as mod


def _write_csv_gz(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    with gzip.open(path, "wt", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


class EditionsScopeAuditTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = mod.REPO_ROOT
        self.editions = json.loads((self.repo / "docs" / "data" / "editions.json").read_text(encoding="utf-8"))
        self.summary_path = self.repo / "data" / "kernel_backbone_summary.json"
        self.spec_path = self.repo / "SPEC.md"
        self.tracker_path = self.repo / "docs" / "tracker.html"

    def _run_with_mutated_editions(self, mutate_fn) -> dict:
        mutated = copy.deepcopy(self.editions)
        mutate_fn(mutated)
        with tempfile.TemporaryDirectory() as td:
            ed_path = Path(td) / "editions.json"
            ed_path.write_text(json.dumps(mutated), encoding="utf-8")
            return mod.audit_editions(ed_path, self.summary_path, self.spec_path, self.tracker_path)

    def test_repo_editions_pass_standalone(self) -> None:
        res = mod.audit_editions(
            self.repo / "docs" / "data" / "editions.json",
            self.summary_path,
            self.spec_path,
            self.tracker_path,
        )
        self.assertTrue(res["pass"], res["errors"])
        self.assertIn("project_only_proof_cone_scope", res["checks"])
        self.assertIn("tracker_caption_parity", res["checks"])

    def test_catches_alpoge_code_lines_unit_mixing(self) -> None:
        # Regression guard for f822b88: Alpoge decl lines placed in Code lines row.
        def mutate(d: dict) -> None:
            for r in d["rows"]:
                if r["label"] == "Code lines (no comments or blanks)":
                    r["values"][0] = 10737728

        res = self._run_with_mutated_editions(mutate)
        self.assertFalse(res["pass"])
        self.assertTrue(any("Code lines" in e for e in res["errors"]))

    def test_catches_alpoge_full_cone_vs_project_only_scope_drift(self) -> None:
        # Regression guard for 7c00919: full 1,484,729 cone mixed next to project-only grh counts.
        def mutate(d: dict) -> None:
            for r in d["rows"]:
                if r["label"] == "Constants in the proof cone":
                    r["values"][0] = 1484729

        res = self._run_with_mutated_editions(mutate)
        self.assertFalse(res["pass"])
        self.assertTrue(any("full library-inclusive cone" in e for e in res["errors"]))

    def test_catches_alpoge_decls_confused_with_constants(self) -> None:
        # Regression guard for 81bd3af: 804,912 declarations placed in Constants row.
        def mutate(d: dict) -> None:
            for r in d["rows"]:
                if r["label"] == "Constants in the proof cone":
                    r["values"][0] = 804912

        res = self._run_with_mutated_editions(mutate)
        self.assertFalse(res["pass"])
        self.assertTrue(any("Constants in the proof cone" in e for e in res["errors"]))

    def test_catches_false_mathlib_archive_scope_claim(self) -> None:
        # Regression guard for 7c00919 / 27ba666.
        def mutate(d: dict) -> None:
            d["alpoge_archive_scope"] = "175,187 files under src/, including 136,266 Mathlib files."

        res = self._run_with_mutated_editions(mutate)
        self.assertFalse(res["pass"])
        self.assertTrue(any("136,266" in e for e in res["errors"]))

    def test_catches_generated_at_predating_pairing_measured_at(self) -> None:
        # Regression guard for ef3be35.
        def mutate(d: dict) -> None:
            d["generated_at"] = "2026-11-26T12:05:44+09:00"

        res = self._run_with_mutated_editions(mutate)
        self.assertFalse(res["pass"])
        self.assertTrue(any("predates" in e for e in res["errors"]))

    def test_catches_export_inversion_and_ratio_drift(self) -> None:
        def mutate(d: dict) -> None:
            d["export_inversion"]["compact_vs_readable_export_pct"] = 99.9
            for r in d["rows"]:
                if r["label"] == "Non-whitespace characters per code line":
                    r["values"][1] = 10.0

        res = self._run_with_mutated_editions(mutate)
        self.assertFalse(res["pass"])
        self.assertTrue(any("compact_vs_readable_export_pct" in e for e in res["errors"]))
        self.assertTrue(any("non_ws/code_lines" in e for e in res["errors"]))

    def test_catches_tracker_caption_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            tracker = Path(td) / "tracker.html"
            tracker.write_text(
                self.tracker_path.read_text(encoding="utf-8").replace("214,545", "999,999"),
                encoding="utf-8",
            )
            res = mod.audit_editions(
                self.repo / "docs" / "data" / "editions.json",
                self.summary_path,
                self.spec_path,
                tracker,
            )
            self.assertFalse(res["pass"])
            self.assertTrue(any("docs/tracker.html: caption" in e for e in res["errors"]))

    def test_strip_lean_comments_and_tree_reproduction(self) -> None:
        sample = (
            "-- full line comment ; ignored\n"
            "/- outer /- nested -/ still comment ; -/\n"
            "theorem foo : \"-- not a comment /- ok\" = \"x\" := by\n"
            "  simp; rfl -- trailing comment\n"
            "\n"
        )
        stripped = mod.strip_lean_comments(sample)
        self.assertNotIn("ignored", stripped)
        self.assertNotIn("nested", stripped)
        self.assertNotIn("trailing", stripped)
        self.assertIn('"-- not a comment /- ok"', stripped)

        with tempfile.TemporaryDirectory() as td:
            src = Path(td) / "src"
            src.mkdir()
            (src / "A.lean").write_text(sample, encoding="utf-8")
            (src / "B.lean").write_text("def χ : Nat := 1\n", encoding="utf-8")
            measured = mod.scan_lean_tree(src)
            self.assertEqual(measured["files"], 2)
            self.assertEqual(measured["raw_lines"], 6)
            self.assertEqual(measured["code_lines"], 3)
            self.assertEqual(measured["semis"], 1)
            self.assertGreater(measured["bytes"], len(sample) + len("def χ : Nat := 1\n"))

            # Build a minimal valid fixture where grh_compact matches measured tree metrics
            mutated = copy.deepcopy(self.editions)
            for row_label, key in mod.TREE_ROW_KEYS:
                for r in mutated["rows"]:
                    if r["label"] == row_label:
                        r["values"][2] = measured[key]
            # Keep pairing and export_inversion consistent with mutated grh_compact files/code_lines
            mutated["cross_repo_pairing"]["compact_modules"] = measured["files"]
            mutated["cross_repo_pairing"]["common_path_modules"] = 1
            mutated["cross_repo_pairing"]["grh_only_total"] = mutated["cross_repo_pairing"]["grh_modules"] - 1
            mutated["cross_repo_pairing"]["compact_only_total"] = measured["files"] - 1
            mutated["cross_repo_pairing"]["compact_only_covered"] = 1
            mutated["cross_repo_pairing"]["non_identical_pairs_accepted"] = 1
            mutated["cross_repo_pairing"]["high_confidence_pairs"] = 1
            mutated["cross_repo_pairing"]["high_confidence_genuine_shorter"] = 1
            mutated["cross_repo_pairing"]["high_confidence_1to1_genuine_shorter"] = 1
            cl_r = next(r["values"][1] for r in mutated["rows"] if r["label"] == "Code lines (no comments or blanks)")
            mutated["export_inversion"]["compact_vs_readable_code_lines_pct"] = round(
                (measured["code_lines"] - cl_r) * 100.0 / cl_r, 1
            )
            ed_path = Path(td) / "editions.json"
            ed_path.write_text(json.dumps(mutated), encoding="utf-8")
            res = mod.audit_editions(
                ed_path,
                self.summary_path,
                self.spec_path,
                self.tracker_path,
                tree_specs=[("grh_compact", src)],
            )
            self.assertTrue(res["pass"], res["errors"])
            self.assertIn("lean_tree_reproduction", res["checks"])

    def test_synthetic_alpoge_export_reproduction_and_mismatch_detection(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            exp = Path(td) / "export"
            exp.mkdir()
            _write_csv_gz(
                exp / "directories.csv.gz",
                ["dir", "level", "files", "lines", "decls_in_cone", "lines_in_cone"],
                [
                    {"dir": "src/Development", "level": "1", "files": 100, "lines": 1000, "decls_in_cone": 2, "lines_in_cone": 30},
                    {"dir": "src/Main.lean", "level": "1", "files": 1, "lines": 12, "decls_in_cone": 1, "lines_in_cone": 5},
                    {"dir": "src/Development/Sub", "level": "2", "files": 50, "lines": 500, "decls_in_cone": 1, "lines_in_cone": 15},
                ],
            )
            _write_csv_gz(
                exp / "decls.csv.gz",
                ["decl", "origin", "lines", "in_cone"],
                [
                    {"decl": "A", "origin": "project", "lines": 10, "in_cone": "true"},
                    {"decl": "B", "origin": "project", "lines": 20, "in_cone": "true"},
                    {"decl": "C", "origin": "project", "lines": 5, "in_cone": "true"},
                    {"decl": "Dead", "origin": "project", "lines": 99, "in_cone": "false"},
                ],
            )
            _write_csv_gz(
                exp / "constants.csv.gz",
                ["name", "origin", "in_cone"],
                [
                    {"name": "p1", "origin": "project", "in_cone": "true"},
                    {"name": "p2", "origin": "project", "in_cone": "true"},
                    {"name": "p3", "origin": "project", "in_cone": "true"},
                    {"name": "p4", "origin": "project", "in_cone": "true"},
                    {"name": "m1", "origin": "mathlib", "in_cone": "true"},
                    {"name": "c1", "origin": "core", "in_cone": "true"},
                    {"name": "c2", "origin": "core", "in_cone": "false"},
                ],
            )
            rep = mod.reproduce_alpoge_export(exp)
            self.assertEqual(rep["files"], 101)
            self.assertEqual(rep["raw_lines"], 1012)
            self.assertEqual(rep["decls_in_cone"], 3)
            self.assertEqual(rep["decl_lines_in_cone"], 35)
            self.assertEqual(rep["project_cone_constants"], 4)
            self.assertEqual(rep["full_cone_constants"], 6)
            self.assertEqual(rep["library_cone_constants"], 2)
            self.assertEqual(rep["non_src_top_dirs"], [])

            # Against the real repo's editions.json, tiny synthetic counts must fail loudly.
            res = mod.audit_editions(
                self.repo / "docs" / "data" / "editions.json",
                self.summary_path,
                self.spec_path,
                self.tracker_path,
                alpoge_export_dir=exp,
            )
            self.assertFalse(res["pass"])
            self.assertTrue(any("alpoge-export: editions.json" in e for e in res["errors"]))

    def test_cli_json_out_and_missing_file_exit2(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            out_json = Path(td) / "report.json"
            rc = mod.main(["--json-out", str(out_json)])
            self.assertEqual(rc, 0)
            payload = json.loads(out_json.read_text(encoding="utf-8"))
            self.assertTrue(payload["pass"])
            rc_err = mod.main(["--editions", str(Path(td) / "missing.json")])
            self.assertEqual(rc_err, 2)


if __name__ == "__main__":
    unittest.main(verbosity=1)

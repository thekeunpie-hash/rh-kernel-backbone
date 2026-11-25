#!/usr/bin/env python3
"""Static Lean 4 TCB, Anti-Slop & Anti-Cheat Auditor (zero-dependency Python 3.11+ stdlib).

Scans all `*.lean` files under a target directory (default: `<root>/src` if present, else `<root>`)
using:
  1. Pre-strip raw Trojan-Source BiDi / zero-width Unicode scan.
  2. Single-pass character state machine (preserving exact line numbers) handling nested
     `/- ... -/` block comments, `--` line comments, `"..."` strings with `\\` escapes, and
     `'...'` char literals (without misparsing Lean identifier prime suffixes like `x'`).
  3. Forbidden token & construct checks:
     - `sorry`, `admit`, `sorryAx`, `evalSorry`
     - custom `axiom` declarations
     - `opaque`, `unsafe`, `partial` declarations
     - `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler`
     - `@[implemented_by]`, `@[extern]`, `attribute [implemented_by|extern]`
     - `skipKernelTC`, `set_option debug.*`
     - `set_option backward.*`, `set_option (synthInstance.)?maxHeartbeats`,
       `set_option pp.explicit` / `pp.all`
     - standalone `import Mathlib` monoliths
     - metaprogramming env escapes (`Lean.addDecl`, `Lean.modifyEnv`, `run_cmd`, `run_elab`, `run_meta`)

Supports `--self-test` to run isolated failure-injection & non-false-positive unit tests in a
temporary directory (cleaned up automatically).
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

BIDI_CHARS_RE = re.compile(r"[\u202a-\u202e\u2066-\u2069\u200b-\u200f\ufeff]")

IDENT_CHAR_RE = re.compile(r"[A-Za-z0-9_'₀-₉ₐ-ₙᵢ-ᵥ]")

# Command boundary: start of line, `;`, or `in` modifier prefix.
CMD_PREFIX = (
    r"(?:^|;|(?<![A-Za-z0-9_'₀-₉])in\b)"
    r"\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|local|noncomputable|unsafe|public|meta)\s+)*"
)

FORBIDDEN_RULES: list[tuple[str, re.Pattern[str]]] = [
    (
        "sorry_or_admit",
        re.compile(
            r"(?<![A-Za-z0-9_'₀-₉])(?:sorry|admit|sorryAx|evalSorry)(?![A-Za-z0-9_'₀-₉])"
            r"|«(?:sorry|admit|sorryAx)»"
        ),
    ),
    (
        "custom_axiom",
        re.compile(CMD_PREFIX + r"axiom(?![A-Za-z0-9_'₀-₉])", re.MULTILINE),
    ),
    (
        "opaque_unsafe_partial",
        re.compile(
            CMD_PREFIX + r"(?:unsafe|opaque|partial)(?![A-Za-z0-9_'₀-₉])"
            r"|(?<![A-Za-z0-9_'₀-₉])unsafe\s+(?:def|axiom|inductive|structure|class|instance|opaque|abbrev|theorem)(?![A-Za-z0-9_'₀-₉])"
            r"|(?<![A-Za-z0-9_'₀-₉])partial\s+(?:def|private|protected|noncomputable|unsafe|instance|abbrev)(?![A-Za-z0-9_'₀-₉])",
            re.MULTILINE,
        ),
    ),
    (
        "native_decide_or_compiler_axiom",
        re.compile(
            r"(?<![A-Za-z0-9_'₀-₉])(?:native_decide|(?:Lean\.)?ofReduceBool|(?:Lean\.)?trustCompiler)(?![A-Za-z0-9_'₀-₉])"
        ),
    ),
    (
        "extern_or_implemented_by",
        re.compile(
            r"@\[[^\]]*\b(?:extern|implemented_by)\b[^\]]*\]"
            r"|\battribute\s*\[[^\]]*\b(?:extern|implemented_by)\b[^\]]*\]"
        ),
    ),
    (
        "skip_kernel_tc_or_debug_option",
        re.compile(
            r"(?<![A-Za-z0-9_'₀-₉])skipKernelTC(?![A-Za-z0-9_'₀-₉])"
            r"|\bset_option\s+debug\.[A-Za-z0-9_.]+"
        ),
    ),
    (
        "backward_option",
        re.compile(r"\bset_option\s+backward\.[A-Za-z0-9_.]+"),
    ),
    (
        "max_heartbeats_override",
        re.compile(r"\bset_option\s+(?:synthInstance\.)?maxHeartbeats(?![A-Za-z0-9_'₀-₉])"),
    ),
    (
        "pp_explicit_or_all",
        re.compile(r"\bset_option\s+pp\.(?:explicit|all)(?![A-Za-z0-9_'₀-₉])"),
    ),
    (
        "import_mathlib_monolith",
        re.compile(
            r"^\s*(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+Mathlib\s*$",
            re.MULTILINE,
        ),
    ),
    (
        "metaprog_env_escape",
        re.compile(
            r"(?<![A-Za-z0-9_'₀-₉])(?:(?:Lean\.)?(?:addDecl|modifyEnv)|run_cmd|run_elab|run_meta)(?![A-Za-z0-9_'₀-₉])"
        ),
    ),
]


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    rule: str
    snippet: str


def _is_ident_char(ch: str) -> bool:
    return bool(ch) and bool(IDENT_CHAR_RE.match(ch))


def _match_char_literal_end(text: str, i: int) -> int | None:
    """If `text[i:]` starts a Lean char literal `'...'`, return index after closing `'`, else None."""
    n = len(text)
    if i >= n or text[i] != "'":
        return None
    if i > 0 and _is_ident_char(text[i - 1]):
        # Prime suffix on an identifier like `x'`, `hs0'`, `f''`
        return None
    if i + 1 >= n:
        return None
    nxt = text[i + 1]
    if nxt in ("\n", "\r", "'"):
        return None
    if nxt == "\\":
        j = i + 2
        if j >= n or text[j] in ("\n", "\r"):
            return None
        j += 1
        while j < n and text[j] not in ("'", "\n", "\r") and j - i <= 10:
            j += 1
        if j < n and text[j] == "'":
            return j + 1
        return None
    if i + 2 < n and text[i + 2] == "'":
        return i + 3
    return None


def strip_comments_and_strings(text: str) -> str:
    """Single-pass character state machine preserving exact line numbers."""
    out: list[str] = []
    n = len(text)
    i = 0
    comment_depth = 0
    in_line_comment = False
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if comment_depth > 0:
            if ch == "/" and nxt == "-":
                comment_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                comment_depth -= 1
                out.append("  ")
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if in_string:
            if ch == "\\":
                if i + 1 < n:
                    if text[i + 1] == "\n":
                        out.append(" \n")
                    else:
                        out.append("  ")
                    i += 2
                else:
                    out.append(" ")
                    i += 1
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue
        if ch == "/" and nxt == "-":
            comment_depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        if ch == "'":
            end_idx = _match_char_literal_end(text, i)
            if end_idx is not None:
                out.append(" " * (end_idx - i))
                i = end_idx
                continue

        out.append(ch)
        i += 1

    return "".join(out)


def scan_text(text: str, rel_path: str) -> list[Finding]:
    findings: list[Finding] = []

    for m in BIDI_CHARS_RE.finditer(text):
        line_no = text.count("\n", 0, m.start()) + 1
        findings.append(
            Finding(
                path=rel_path,
                line=line_no,
                rule="trojan_bidi_unicode",
                snippet=f"U+{ord(m.group(0)):04X}",
            )
        )

    stripped = strip_comments_and_strings(text)
    lines = stripped.splitlines()

    for rule_name, pattern in FORBIDDEN_RULES:
        for m in pattern.finditer(stripped):
            line_no = stripped.count("\n", 0, m.start()) + 1
            snippet = lines[line_no - 1].strip() if 0 <= line_no - 1 < len(lines) else m.group(0).strip()
            findings.append(
                Finding(
                    path=rel_path,
                    line=line_no,
                    rule=rule_name,
                    snippet=snippet[:120],
                )
            )

    return findings


def scan_tree(scan_root: Path, rel_base: Path) -> tuple[int, list[Finding]]:
    lean_files = sorted(
        p for p in scan_root.rglob("*.lean")
        if ".lake" not in p.parts
    )
    all_findings: list[Finding] = []
    for lf in lean_files:
        rel = str(lf.relative_to(rel_base))
        text = lf.read_text(encoding="utf-8", errors="replace")
        all_findings.extend(scan_text(text, rel))
    return len(lean_files), all_findings


def run_self_test() -> int:
    print("Running lean_anti_cheat_audit.py --self-test ...")
    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="lean_anticheat_selftest_") as td:
        tmp = Path(td)

        clean_samples: dict[str, str] = {
            "clean_comments_strings.lean": (
                "-- sorry admit axiom partial unsafe opaque\n"
                "/- nested /- sorry axiom native_decide -/ backward.isDefEq.respectTransparency -/\n"
                "/-- docstring with `sorry` and `import Mathlib` -/\n"
                "def s1 : String := \"-- sorry /- axiom -/ \\\" sorry \\\"\"\n"
                "def c1 : Char := '\"'\n"
                "def c2 : Char := '\\''\n"
                "def sorry_helper (axiom_count partial_sum : Nat) : Nat := axiom_count + partial_sum\n"
                "theorem h' (x' : Nat) : x' = x' := rfl\n"
                "import Mathlib.NumberTheory.LSeries.DirichletContinuation\n"
            ),
            "clean_primes_and_attrs.lean": (
                "def IsPartial (n : Nat) : Bool := n == 0\n"
                "def extern_val : Nat := 1\n"
                "def debug_flag : Bool := false\n"
                "@[simp] theorem foo (hs0' : True) : True := hs0'\n"
            ),
        }

        for name, body in clean_samples.items():
            p = tmp / name
            p.write_text(body, encoding="utf-8")
            hits = scan_text(p.read_text(encoding="utf-8"), name)
            if hits:
                failures.append(f"False positive in {name}: {hits}")

        bad_samples: list[tuple[str, str, str]] = [
            ("bad_sorry.lean", "theorem t : False := by sorry\n", "sorry_or_admit"),
            ("bad_admit.lean", "theorem t : False := by admit\n", "sorry_or_admit"),
            ("bad_sorryAx.lean", "theorem t : False := sorryAx False\n", "sorry_or_admit"),
            ("bad_axiom.lean", "axiom evil : False\n", "custom_axiom"),
            ("bad_semi_axiom.lean", "def ok := 1; axiom evil : False\n", "custom_axiom"),
            ("bad_opaque.lean", "opaque foo : Nat\n", "opaque_unsafe_partial"),
            ("bad_unsafe.lean", "unsafe def foo : Nat := 0\n", "opaque_unsafe_partial"),
            ("bad_partial.lean", "partial def loop : Nat := loop\n", "opaque_unsafe_partial"),
            ("bad_native_decide.lean", "theorem t : 1 = 1 := by native_decide\n", "native_decide_or_compiler_axiom"),
            ("bad_ofReduceBool.lean", "theorem t := Lean.ofReduceBool\n", "native_decide_or_compiler_axiom"),
            ("bad_trustCompiler.lean", "theorem t := Lean.trustCompiler\n", "native_decide_or_compiler_axiom"),
            ("bad_impl_by.lean", "@[implemented_by foo] def bar : Nat := 0\n", "extern_or_implemented_by"),
            ("bad_extern.lean", "@[extern \"c_fn\"] def bar : Nat := 0\n", "extern_or_implemented_by"),
            ("bad_attr_impl.lean", "attribute [implemented_by foo] bar\n", "extern_or_implemented_by"),
            ("bad_skip_tc.lean", "set_option debug.skipKernelTC true\n", "skip_kernel_tc_or_debug_option"),
            ("bad_debug.lean", "set_option debug.trace true\n", "skip_kernel_tc_or_debug_option"),
            ("bad_backward.lean", "set_option backward.isDefEq.respectTransparency false\n", "backward_option"),
            ("bad_heartbeats.lean", "set_option maxHeartbeats 1000000\n", "max_heartbeats_override"),
            ("bad_synth_hb.lean", "set_option synthInstance.maxHeartbeats 200000\n", "max_heartbeats_override"),
            ("bad_pp_explicit.lean", "set_option pp.explicit true\n", "pp_explicit_or_all"),
            ("bad_pp_all.lean", "set_option pp.all true\n", "pp_explicit_or_all"),
            ("bad_import_mathlib.lean", "public import Mathlib -- full\n", "import_mathlib_monolith"),
            ("bad_import_all.lean", "import all Mathlib\n", "import_mathlib_monolith"),
            ("bad_addDecl.lean", "def f := Lean.addDecl\n", "metaprog_env_escape"),
            ("bad_run_cmd.lean", "run_cmd pure ()\n", "metaprog_env_escape"),
            ("bad_bidi.lean", "-- hidden \u202e sorry\n", "trojan_bidi_unicode"),
            ("bad_after_char.lean", "def q : Char := '\"'\ntheorem t : False := by sorry\n", "sorry_or_admit"),
        ]

        for name, body, expected_rule in bad_samples:
            p = tmp / name
            p.write_text(body, encoding="utf-8")
            hits = scan_text(p.read_text(encoding="utf-8"), name)
            rules = {h.rule for h in hits}
            if expected_rule not in rules:
                failures.append(f"Missed {expected_rule} in {name}: got {hits}")

        line_test = (
            "/- line 1\n"
            "   line 2\n"
            "   line 3 -/\n"
            "def s := \"a\nb\"\n"
            "theorem real_line_6 : False := by sorry\n"
        )
        p_line = tmp / "line_no.lean"
        p_line.write_text(line_test, encoding="utf-8")
        hits_line = scan_text(p_line.read_text(encoding="utf-8"), "line_no.lean")
        if not hits_line or hits_line[0].line != 6:
            failures.append(f"Line number mismatch: expected 6, got {hits_line}")

    if failures:
        for f in failures:
            print(f"[FAIL] {f}", file=sys.stderr)
        return 1

    print("[PASS] lean_anti_cheat_audit self-test passed (2 clean + 27 injection + line-number checks).")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="Path to Lean 4 project root directory (default: current working directory)",
    )
    ap.add_argument(
        "--dir",
        type=str,
        default=None,
        help="Optional subdirectory under --root to scan (default: 'src' if it exists, else root)",
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="Run built-in failure-injection and false-positive unit tests in a temp dir",
    )
    args = ap.parse_args()

    if args.self_test:
        return run_self_test()

    root = args.root.resolve()
    if args.dir:
        scan_root = root / args.dir
    elif (root / "src").is_dir():
        scan_root = root / "src"
    else:
        scan_root = root

    if not scan_root.is_dir():
        print(f"[FAIL] Missing target directory: {scan_root}", file=sys.stderr)
        return 1

    count, findings = scan_tree(scan_root, root)
    if count == 0:
        print(f"[FAIL] No .lean files found under {scan_root}", file=sys.stderr)
        return 1

    if findings:
        print(f"[FAIL] Found {len(findings)} forbidden construct(s) across {count} source files:", file=sys.stderr)
        for f in findings:
            print(f"  {f.path}:{f.line}: [{f.rule}] {f.snippet}", file=sys.stderr)
        return 1

    print(f"[PASS] Lean anti-cheat audit clean across {count} .lean file(s) in {scan_root}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

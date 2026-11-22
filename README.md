# Kernel-Grounded Minimal Backbone Specification (`leanprover-community/riemann-hypothesis`)

> **Interactive Web Edition (GitHub Pages)**: [thekeunpie-hash.github.io/rh-kernel-backbone](https://thekeunpie-hash.github.io/rh-kernel-backbone/)  
> **Full Specification**: [SPEC.md](SPEC.md) · **Machine-Readable Kernel Summary**: [data/kernel_backbone_summary.json](data/kernel_backbone_summary.json) · **Zero-Dead-Citation Auditor**: [scripts/audit_spec_citations.py](scripts/audit_spec_citations.py)

A compact, kernel-audited technical map of Levent Alpöge's Lean `v4.33.1` formalization of the Riemann Hypothesis and Dirichlet $L$-function GRH ([`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis)), grounded directly in Andrew Sutherland and James Shore's `v0.2.1` Lean kernel export (`cone-constants.txt.gz`, `decls.csv.gz`, `dominators.tsv.gz`, `why-parents.csv.gz`, `directories.csv.gz`).

## Epistemic Protocol

Every substantive claim in [SPEC.md](SPEC.md) is fenced with one of three explicit labels:

- **`[Exact]`** — Mechanically computed from the `v0.2.1` Lean kernel export or directly verified by Lean `v4.33.1` (`Kernel.isDefEq`, `Meta.isDefEq`, `collectAxioms`, `-DwarningAsError=true`).
- **`[Verified]`** — Read directly from the pinned Lean `v4.33.1` source and confirmed `in_cone = true` in `decls.csv.gz`.
- **`[Reading]`** — Informal mathematical synthesis connecting verified Lean signatures to number theory and automorphic forms.

Every active qualified Lean declaration cited outside the fenced Dead-Code Self-Audit in Section 7 of [SPEC.md](SPEC.md) is mechanically checked against `decls.csv.gz` and `cone-constants.txt.gz` with **0 dead citations**.

## Key Kernel-Export Findings `[Exact]`

| Metric | Value | Notes |
| :--- | ---: | :--- |
| Upstream source tree | 175,187 files · 17,374,215 raw lines | 1,063,284 parsed declarations (13,432,480 decl lines) |
| Active Lean kernel cone (`in_cone = true`) | **146,287 files · 10,737,728 decl lines** | **804,912 active decls** (75.7% of decls, 61.8% of raw lines); `1,484,729` kernel constants |
| Wholly dead files (`used_decls = 0`) | 28,900 files · 1,754,237 decl lines | Plus 940,515 dead decl lines inside mixed active files |
| Shared across all 5 `Main.lean` theorems | **804,887 decls · 10,737,528 decl lines** | **99.997% of the cone**, routed through one root chokepoint: `allChi` (`src/Supplements/Kernels/MainTheorems.lean:7`) |
| Single-declaration active files | 63,899 files (43.7% of active files) | 48,922 of those are `≤ 15` decl lines (`213,750` decl lines total) |
| Axioms | `{propext, Classical.choice, Quot.sound}` | Verified by Andrew Sutherland's [MIT audit](https://math.mit.edu/~drew/grh/audit.log) |

### Three Static-Analysis Traps Resolved by the Kernel Cone

1. **Behrend sets (`Formalism/BehrendSets/` is `0/89` dead `[Exact]`)**: The standalone `src/Formalism/BehrendSets/` directory never enters the kernel proof terms. The live proof constructs Behrend-free thick sets directly from Mathlib's `Behrend.exists_large_sphere` inside `Formalism.FrobeniusOrbits.hostThickExists` (`ThickExists.lean:181`, constant $C = 32$, depth 14) and performs non-uniform coset-biased Bernoulli selection in `src/Development/AutomorphicArithmetic/ThickFrames/` (`69/69` decls active: `thickFrame2`, `select`, `topsChoiceH`) `[Verified]`.
2. **Iwasawa descent without $\mathbb{Z}_p[[T]]$ (`IwasawaModules/` is `0/16` dead `[Exact]`)**: Formal power-series ring theory over $\mathbb{Z}_p[[T]]$ is unused in the cone. Instead, `UpperTheory.V.FW.ferreroWashington` (`170/170` decls active) gives a finite $\mathbb{Z}_\ell$-generator bound `Tower.IsTower l L R` on the unramified Iwasawa module, and `UpperTheory.V.PropA.{exists_centres_norm, aBound_of_descends}` lifts $\gamma^{\ell^j}$ to an $R \times R$ matrix over $\mathbb{Z}_\ell$ and factors its determinant over $\overline{\mathbb{Q}}_\ell$ to dodge at most $R$ exceptional $\ell$-adic centers (`Win.thmBab_of_lemmaK`) `[Verified]`.
3. **Standalone corollaries & clone asymmetry**: `SmallClassNumbers` (`0/23` decls active) is outside the 5-theorem kernel cone (and removed upstream). In `UnitaryGroupMassFormula`, the three near-duplicate directories have starkly asymmetric kernel usage: `StabilizerVolume` is **95.5%** active (`15,186 / 15,895` L), `StabilizerOrbitVolume` is **34.7%** active (`5,407 / 15,600` L), and `WeilStabilizerVolume` is **0.9%** active (`135 / 14,668` L — 99.1% dead) `[Exact]`.

## Upstream Lean `v4.33.1` Simplification PRs

All five rewritten files below are 100%-kernel-used (`in_cone = true`), verified locally under Lean `v4.33.1` (`-j1`, `-DwarningAsError=true`, `Kernel.isDefEq = true`, `Meta.isDefEq = true` on every declaration type and `def` value, exact `BinderInfo`/`levelParams`/imports, `{propext, Classical.choice, Quot.sound}` only, and clean compilation of all direct `dist=1` importers):

- [PR #60](https://github.com/leanprover-community/riemann-hypothesis/pull/60) (**merged**, `173225e84`) — `CapelliIdentities/FixPiIff.lean` (`8,029 → 45` lines, `-99.4%`, `86.36s → 70.78s`).
- [PR #65](https://github.com/leanprover-community/riemann-hypothesis/pull/65) (open) — 4 remaining unclaimed kernel-used `CapelliIdentities` files (`FreeModuleQuotient.lean`, `ContDiffHerm.lean`, `SquareOfApproximation.lean`, `LimitOfFinite.lean`: `5,073 → 591` lines, `-88.4%`, `105 → 0` warnings).

## Independent Verification & TCB Audit Summary `[Exact]`

- **Four independent kernels accept the exported proof** (Andrew Sutherland, [MIT verification page](https://math.mit.edu/~drew/grh/), 2026-11-22 03:10 UTC): `leanchecker` (`175,187/175,187`), `lean4lean` (`175,187/175,187`), `nanoda` (Rust, full `61.57 GB` export, `exit 0`), `con-leche --compare` (`1,468,418` decls, all 5 `Main.lean` theorems justified against `Challenge.lean`), and `con-ron --compare` (Rust port, `exit 0`).
- **Zeta-free arithmetic check (`Robin1984`)**: Combining the proof with `kimihiro64/Robin1984` proves `robin_inequality` and `lagarias_inequality` using only `{propext, Classical.choice, Quot.sound}`, accepted by `con-leche --compare`, `con-ron --compare` (`1,472,825` decls), and `nanoda`.
- **Zero TCB bypasses**: Upstream `verification/static-scan.txt` and our line-by-line metaprogramming audit ([`meta_audit_verdict.md`](https://github.com/thekeunpie-hash/rh-lean-dissection/blob/main/reports/meta_audit_verdict.md)) confirm 0 `axiom`, 0 `sorry`, 0 `native_decide`/`ofReduceBool`/`trustCompiler`, 0 `implemented_by`/`extern`/`unsafe`/`opaque`, and 0 `skipKernelTC` across all 175,187 files. See Section 8 of [SPEC.md](SPEC.md) for the complete TCB breakdown.

## Reproduce the Zero-Dead-Citation Audit

Download `cone-constants.txt.gz` and `decls.csv.gz` from James Shore's `v0.2.1` kernel export, then run:

```sh
python scripts/audit_spec_citations.py \
  --cone path/to/cone-constants.txt.gz \
  --decls path/to/decls.csv.gz \
  SPEC.md README.md
```

Expected result: `[PASS]` with `dead=0` on both files.

## Repository Layout

| Path | Description |
| :--- | :--- |
| [SPEC.md](SPEC.md) | Full kernel-grounded Minimal Backbone Specification (dominator spine, 3 pillars, 16-row witness table, and 24-item dead-code self-audit) |
| [docs/index.html](docs/index.html) | Interactive web edition served via GitHub Pages (KaTeX typesetting, bloat waterfall, 36-landmark witness-chain explorer, searchable top-60 dominator table) |
| [data/kernel_backbone_summary.json](data/kernel_backbone_summary.json) | Machine-readable global accounting, directory/subtree usage, top dominators, and 36 exact `why-parents` chains |
| [scripts/audit_spec_citations.py](scripts/audit_spec_citations.py) | Zero-dependency Python auditor checking every active qualified Lean identifier against `cone-constants.txt.gz` and `decls.csv.gz` |
| [LICENSE](LICENSE) | MIT License |

For the broader Round 1–2 static dissection, metaprogramming soundness audit, standalone Lean harnesses, and Korean archives, see [`thekeunpie-hash/rh-lean-dissection`](https://github.com/thekeunpie-hash/rh-lean-dissection).

# Kernel-Grounded Minimal Backbone Specification (`leanprover-community/riemann-hypothesis`)

> **Interactive Web Edition & Live Upstream Tracker (GitHub Pages)**: [thekeunpie-hash.github.io/rh-kernel-backbone](https://thekeunpie-hash.github.io/rh-kernel-backbone/)  
> **Full Specification**: [SPEC.md](SPEC.md) · **Live Tracker JSON (Hourly CI)**: [data/upstream_frontier.json](data/upstream_frontier.json) · **Machine-Readable Kernel Summary**: [data/kernel_backbone_summary.json](data/kernel_backbone_summary.json) · **Citation Auditor**: [scripts/audit_spec_citations.py](scripts/audit_spec_citations.py) · **NDJSON Statement Auditor**: [scripts/audit_ndjson_statement.py](scripts/audit_ndjson_statement.py)

A compact, kernel-audited technical map **and auto-updating hourly upstream progress tracker** for Levent Alpöge's formalization of the Riemann Hypothesis and Dirichlet $L$-function GRH ([`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis), baseline `v0.2.1` on Lean `v4.33.1`, live `main` now on Lean `v4.36.0` after [PR #66](https://github.com/leanprover-community/riemann-hypothesis/pull/66)), grounded directly in Andrew Sutherland and James Shore's `v0.2.1` Lean kernel export (`cone-constants.txt.gz`, `decls.csv.gz`, `dominators.tsv.gz`, `why-parents.csv.gz`, `directories.csv.gz`).

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

## Upstream Lean `v4.33.1` & `v4.36.0` Simplification & Modernization PRs

Every file modified across our six upstream PRs below is 100%-kernel-used (`in_cone = true`), verified locally under the target official Lean toolchain (`Kernel.isDefEq = true` and `Meta.isDefEq = true` on every exported declaration type and `def` value, exact `BinderInfo`/`levelParams`/export-set parity, `{propext, Classical.choice, Quot.sound}` only, and clean compilation of direct `dist=1` importers):

- [PR #60](https://github.com/leanprover-community/riemann-hypothesis/pull/60) (**merged**, `173225e84`, retained in `v4.36.0` `#66`) — `CapelliIdentities/FixPiIff.lean` (`8,029 → 45` lines, `-99.4%`, `86.36s → 70.78s`).
- [PR #65](https://github.com/leanprover-community/riemann-hypothesis/pull/65) (**merged**, `f1f6d6542`, retained in `v4.36.0` `#66`) — 4 remaining unclaimed kernel-used `CapelliIdentities` files (`FreeModuleQuotient.lean`, `ContDiffHerm.lean`, `SquareOfApproximation.lean`, `LimitOfFinite.lean`: `5,073 → 591` lines, `-88.4%`, `105 → 0` warnings).
- [PR #71](https://github.com/leanprover-community/riemann-hypothesis/pull/71) (**merged to `main` via [PR #115](https://github.com/leanprover-community/riemann-hypothesis/pull/115)**, co-authored commit `da6765973f`, `149,396`-module full build & 4.35 GB public cache verified) — removes **66** `backward.*` compatibility directives (**26 of 33** repo-wide `backward.defeqAttrib.useBackward` hits + **40** `backward.isDefEq.respectTransparency` hits) across 4 kernel-used scheme files (`CofilteredSchemeLimitExistsLocally.lean`, `CoequifiberedDiagramMap.lean`, `RelObjIsoHomSubtype.lean`, `ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint.lean`).
- [PR #109](https://github.com/leanprover-community/riemann-hypothesis/pull/109) (**open on Lean `v4.36.0`**, `0d0a55648`, independently checked `85/85` downstream modules by `@marwuint`) — restores `@antoshashakov`'s rolled-back `#68` shared GL finiteness proof on the Lean `v4.36.0` module-system tree (`AutomorphicFormsFiniteGL.lean` + `180` deleted duplicate modules: `9,744 → 14` lines `-99.86%`, `135,390 → 17` normalized tokens `-99.99%`; `0` warnings, `.olean` equivalence PASS, `9/9` critical `dist=1` importers `exit 0`).
- [PR #110](https://github.com/leanprover-community/riemann-hypothesis/pull/110) (**open on Lean `v4.36.0`**, `5cdd8a23b`) — simplifies both `2,796`-char machine-dumped `@alg` type signatures in `NonzeroPlacesOverPrimesOfLifts.lean` (`cpR`, `std_cpR`) and removes 2 redundant `maxHeartbeats` overrides (`80 → 70` lines, `9,337 → 3,385` bytes `-63.7%`, `2,121 → 610` normalized tokens `-71.2%`; `0` warnings, `4/4` exported decls `.olean` equivalence PASS, `2/2` `dist=1` importers `exit 0`).
- [PR #224](https://github.com/leanprover-community/riemann-hypothesis/pull/224) (**open on Lean `v4.36.0`**, `bca24c2b6`) — eliminates the **final 5 remaining `backward.defeqAttrib.useBackward` directives repo-wide (`33 → 0`)** together with all 6 co-located `backward.isDefEq.respectTransparency` directives across 5 kernel-used files (`ExistsFilteredColimitEtaleOfIndEt.lean`, `ExistsIntegralNbhd.lean`, `CupConnecting.lean`, `DiagonalSuccIsoFreeInvSingle.lean`, `IsIsoNormalizationPullbackOfToIntegralClosure.lean`; `11 → 0` `backward.*`, `119/119` exported decls `.olean`-verified, `9/9` `dist=1` importers `exit 0`).

## Live Upstream `main` Auto-Tracker (Hourly CI) `[Exact]`

A scheduled GitHub Actions workflow ([`.github/workflows/update-tracker.yml`](.github/workflows/update-tracker.yml)) runs [`scripts/update_upstream_tracker.py`](scripts/update_upstream_tracker.py) every hour against live `leanprover-community/riemann-hypothesis:main`, recording exact `.lean` file counts, lines, imports, declarations, remaining `backward.*` / `maxHeartbeats` options, and active Lean `v4.36.0` / `v4.37.0-rc1` PR queue status (`#224`, `#185`, `#134`, `#109`, `#110`, `#120`, `#208`, `#194`, `#88`, `#97`, `#83`, `#87`, plus merged milestones `#115`, `#150`, and donor-worker `#101`) into [`data/upstream_frontier.json`](data/upstream_frontier.json) when upstream metrics change. Following [PR #66](https://github.com/leanprover-community/riemann-hypothesis/pull/66) (`leanprover/lean4:v4.36.0`), [PR #115](https://github.com/leanprover-community/riemann-hypothesis/pull/115) (merging `#71` and cutting `backward.*` from `3,000` to `2,934`), and [PR #150](https://github.com/leanprover-community/riemann-hypothesis/pull/150), live `main` (`51d9b1a28`) stands at **`149,397` files (`-25,790` vs. `v0.2.1`) and `15,168,601` lines (`-2,205,614` / `-12.7%`)**.

## Independent Verification & TCB Audit Summary `[Exact]`

- **Four independent kernels + DeepMind `formal-conjectures` Comparator accept the exported proof**: Andrew Sutherland ([MIT verification page](https://math.mit.edu/~drew/grh/), 2026-11-22 04:35 UTC) verified `leanchecker` (`175,187/175,187`), `lean4lean` (`175,187/175,187`), `nanoda` (Rust, full `61.57 GB` export, `exit 0`), `con-leche --compare` (`1,468,418` decls, all 5 `Main.lean` theorems justified against `Challenge.lean`), and `con-ron --compare` (Rust port, `exit 0`). Separately, [PR #88](https://github.com/leanprover-community/riemann-hypothesis/pull/88) (`@Deicyde`, verified by `@ishaan2006`) passed `con-leche --compare` (`61.57 GB` export, `sha256 17719b54…`) accepting both `RiemannHypothesis.riemannHypothesis` and `GRH.generalized_riemann_hypothesis` against DeepMind's pre-existing `formal-conjectures` definitions.
- **Zeta-free arithmetic check & explicit elaborated statements (`Robin1984` + [`explicit-statements.out`](https://math.mit.edu/~drew/grh/explicit-statements.out))**: Combining the proof with `kimihiro64/Robin1984` proves `robin_inequality` and `lagarias_inequality` using only `{propext, Classical.choice, Quot.sound}`, accepted by `con-leche --compare`, `con-ron --compare` (`1,472,825` decls), and `nanoda`. Elaborated against Mathlib `0df444a3` alone (zero proof loaded), `lagariasStmt` names **27** constants directly (**1,801** declaration closure) and `robinStmt` names **21** constants directly (**2,050** declaration closure).
- **Lean-free raw NDJSON audit ([`scripts/audit_ndjson_statement.py`](scripts/audit_ndjson_statement.py))**: Parses MIT's `challenge.ndjson.zst` (`46.88 MB`, `sha256 bd484ac9…b2b9`, `51,692` top-level records, `0` unsafe, `0` missing) with Python's standard library alone, confirming all 5 raw kernel statement ASTs and `{Classical.choice, Quot.sound, propext}` only (`0` `sorryAx`) across their full statement-type closures (`52,527`–`52,992` declarations).
- **Zero TCB bypasses**: Upstream `verification/static-scan.txt` and our line-by-line metaprogramming audit ([`meta_audit_verdict.md`](https://github.com/thekeunpie-hash/rh-lean-dissection/blob/main/reports/meta_audit_verdict.md)) confirm 0 `axiom`, 0 `sorry`, 0 `native_decide`/`ofReduceBool`/`trustCompiler`, 0 `implemented_by`/`extern`/`unsafe`/`opaque`, and 0 `skipKernelTC` across all 175,187 files. See Section 8 of [SPEC.md](SPEC.md) for the complete TCB breakdown.

## Reproduce the Audits

Download `cone-constants.txt.gz` and `decls.csv.gz` from James Shore's `v0.2.1` kernel export, then run:

```sh
python scripts/audit_spec_citations.py \
  --cone path/to/cone-constants.txt.gz \
  --decls path/to/decls.csv.gz \
  SPEC.md README.md
```

Expected result: `[PASS]` with `dead=0` on both files.

To inspect the five raw kernel headline statements and verify their SHA-256 and axiom closures directly from MIT's `challenge.ndjson.zst` without Lean:

```sh
python scripts/audit_ndjson_statement.py \
  --expected-sha256 bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9 \
  path/to/challenge.ndjson.zst
```

## Repository Layout

| Path | Description |
| :--- | :--- |
| [SPEC.md](SPEC.md) | Full kernel-grounded Minimal Backbone Specification (dominator spine, 3 pillars, 16-row witness table, 24-item dead-code self-audit, and Section 8 multi-kernel / TCB audit) |
| [docs/index.html](docs/index.html) | Interactive web edition served via GitHub Pages (KaTeX typesetting, bloat waterfall, 36-landmark witness-chain explorer, searchable top-60 dominator table) |
| [data/kernel_backbone_summary.json](data/kernel_backbone_summary.json) | Machine-readable global accounting, directory/subtree usage, top dominators, and 36 exact `why-parents` chains |
| [data/upstream_frontier.json](data/upstream_frontier.json) | Auto-updated live upstream `main` metrics (`files`, `lines`, `imports`, `declarations`, `backward.*`, `maxHeartbeats`), PR frontier, verified patterns, and stacked Lean 4.36 PR queue |
| [scripts/update_upstream_tracker.py](scripts/update_upstream_tracker.py) | Hourly CI tracker script measuring live `leanprover-community/riemann-hypothesis:main` and PR queue status (powered by [`.github/workflows/update-tracker.yml`](.github/workflows/update-tracker.yml)) |
| [scripts/audit_spec_citations.py](scripts/audit_spec_citations.py) | Zero-dependency Python auditor checking every active qualified Lean identifier against `cone-constants.txt.gz` and `decls.csv.gz` |
| [scripts/audit_ndjson_statement.py](scripts/audit_ndjson_statement.py) | Zero-dependency Lean-free Python auditor inspecting raw `lean4export 3.1.0` NDJSON statements, safety flags, and axiom closures |
| [LICENSE](LICENSE) | MIT License |

For the broader Round 1–2 static dissection, metaprogramming soundness audit, standalone Lean harnesses, and Korean archives, see [`thekeunpie-hash/rh-lean-dissection`](https://github.com/thekeunpie-hash/rh-lean-dissection).

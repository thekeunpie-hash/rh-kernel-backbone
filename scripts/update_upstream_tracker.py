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
    71: ("portability", "active", 0, "Remove 66 backward.* options across 4 kernel-used scheme files (landed in #115 as da6765973f)"),
    66: ("toolchain-prune", "mixed", 15068, "Bump to Lean & Mathlib v4.36.0, module system, prune 15,068 dead files"),
    115: ("active-refactor", "active", 0, "Merge 53-file reviewed Lean 4.36 cleanup batch (incl. #70, #71, #74-#76, #80-#82, #90, #92)"),
    150: ("active-refactor", "active", 0, "Merge remaining 79-file reviewed Lean 4.36 cleanup batch (incl. #54, #62, #94)"),
    185: ("toolchain-upgrade", "full", 180, "Integrate #134 build speedup + bump to Lean 4.37.0-rc1 & Mathlib 31ce06ea"),
    134: ("performance", "full", 180, "Speed up build (-21.9% CPU): heartbeats 78.8k->2.9k, shake imports, 166 slow proofs, #68"),
    120: ("architecture", "full", 101512, "Collapse 28,169 thin wrappers & consolidate 93,601 modules into 20,258 bundles (-101,512 files)"),
    208: ("active-refactor", "active", 147, "Reuse existing proofs in 41 modules and delete 147 duplicate modules (-22,373 L)"),
    194: ("portability", "full", 0, "Resolve ~10,000 linter and deprecation warnings across 1,864 files"),
    88: ("verification", "statement", 0, "DeepMind formal-conjectures Comparator setup (con-leche --compare ACCEPTED)"),
    97: ("formatting", "full", 0, "Run Lean auto-formatter over 147,418 files in src/ (v4.36)"),
    83: ("active-refactor", "active", 0, "Zero-free region: replace 34-file assembly with 2,447-token proof (Lean 4.36)"),
    87: ("active-refactor", "active", 0, "Shorten checked proofs across 816 Lean modules"),
    101: ("infra", "full", 0, "Let registered donors build bounded proof shards"),
    109: ("active-refactor", "active", 180, "Restore #68 shared GL finiteness proof on Lean 4.36 (-180 files, -9,730 L; 85/85 verified by @marwuint)"),
    110: ("active-refactor", "active", 0, "Simplify explicit type dumps in cpR and std_cpR (NonzeroPlacesOverPrimesOfLifts.lean, -71.2% norm tokens)"),
    221: ("active-refactor", "full", 0, "Consolidate 10+ redundant-proof cleanup PRs on top of #185 (3,076 files, #2 in merge queue)"),
    224: ("portability", "active", 0, "Remove final 5 backward.defeqAttrib.useBackward + 6 respectTransparency directives repo-wide (33 -> 0)"),
}

TRACKED_OPEN_PRS = [224, 185, 221, 134, 109, 110, 120, 208, 194, 88, 97, 83, 87, 150, 115, 71, 101]

# Objective, non-LoC stewardship profiles paired with live GitHub API merged & batch-queue counts.
# `group` strictly reflects GitHub repository access: "collaborator" (COLLABORATOR/MEMBER) vs "contributor".
# `pillars` encodes the 4 non-LoC contribution axes [ci_toolchain, proof_cleanup, debt_infra, audit_triage] (0..3).
STEWARDSHIP_PROFILES = [
    {
        "slug": "kim-em",
        "login": "kim-em",
        "name": "Kim Morrison",
        "initials": "KM",
        "group": "collaborator",
        "github_role": "COLLABORATOR",
        "role": "Lean FRO · Merge Queue & Distributed CI Lead",
        "headline": "Runs distributed AWS + donor-shard CI and lands the linear merge queue (#115, #150 -> #185 -> #221).",
        "impact_badges": ["CI & Merge Queue Lead", "v4.36 / v4.37-rc1"],
        "pillars": [3, 1, 2, 3],
        "non_loc_impact": "Operates multi-machine AWS + donor-shard CI, coordinates linear merge queue (#115, #150 -> #185 -> #221).",
        "governance_signal": "Repo Collaborator · Lean FRO · Merge queue coordinator",
        "bio": "Research software engineer at the Lean Focused Research Organization (Lean FRO) and long-time Mathlib maintainer. On leanprover-community/riemann-hypothesis, he runs the distributed AWS and donor-shard CI fleet, lands reviewed cleanup batches (#115, #150), and coordinates the linear merge queue through the Lean 4.37.0-rc1 upgrade (#185) and stacked consolidations (#221).",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#115 batch", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/115"},
            {"label": "#150 batch", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/150"},
            {"label": "#101 donors", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/101"},
        ],
        "links": [
            {"label": "GitHub @kim-em", "url": "https://github.com/kim-em"},
            {"label": "Merged PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Akim-em+is%3Amerged"},
            {"label": "Donor Shards PR #101", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/101"},
            {"label": "Mathlib4", "url": "https://github.com/leanprover-community/mathlib4"},
        ],
    },
    {
        "slug": "vilin97",
        "login": "Vilin97",
        "name": "Vasily Ilin",
        "initials": "VI",
        "group": "collaborator",
        "github_role": "COLLABORATOR",
        "role": "Toolchain Modernization & Build Performance Lead",
        "headline": "Ported all 175k files to Lean v4.36.0 (#66) and authored the -21.9% CPU speedup (#79/#98/#104 -> #134 -> #185).",
        "impact_badges": ["v4.36.0 Port (#66)", "-21.9% CPU · Queue #1 (#185)"],
        "pillars": [3, 3, 2, 2],
        "non_loc_impact": "Landed Lean v4.36.0 + module system (#66, -15,068 dead files); authored stacked speedup PRs #79/#98/#104 -> #134 (-21.9% CPU, heartbeats 78.8k->2.9k) folded into v4.37-rc1 (#185).",
        "governance_signal": "Repo Collaborator · #1 in merge queue (#185) · v4.36 foundation",
        "bio": "Repo collaborator and large-scale Lean formalization engineer (also active on CFSG) driving toolchain modernization and build performance. He executed the landmark Lean & Mathlib v4.36.0 port with module-system support (#66, pruning 15,068 dead files) and authored the stacked performance series (#79 heartbeat removal, #98 import minimization, #104 slow-proof optimization -> #134, cutting CPU time by 21.9%), now integrated into #185 (Lean 4.37.0-rc1) at #1 in the merge queue.",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#66 v4.36", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66"},
            {"label": "#134 -21.9% CPU", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/134"},
            {"label": "#185 v4.37-rc1", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185"},
        ],
        "links": [
            {"label": "GitHub @Vilin97", "url": "https://github.com/Vilin97"},
            {"label": "Lean v4.36.0 Port #66", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66"},
            {"label": "Build Speedup #134", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/134"},
            {"label": "Lean 4.37-rc1 Integration #185", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185"},
            {"label": "Heartbeat Cleanup #79", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/79"},
        ],
    },
    {
        "slug": "deicyde",
        "login": "Deicyde",
        "name": "Jack McCarthy",
        "initials": "JM",
        "group": "collaborator",
        "github_role": "COLLABORATOR",
        "role": "Batch Queue Triage & Verification Spec Lead",
        "headline": "Built batch-queue triage automation (#226), DeepMind formal-conjectures Comparator (#88), and README specs.",
        "impact_badges": ["Batch Queue Bot (#226)", "Comparator (#88)"],
        "pillars": [2, 1, 2, 3],
        "non_loc_impact": "Built batch queue triage automation (#226), DeepMind formal-conjectures Comparator setup (#88), and README specs.",
        "governance_signal": "Repo Collaborator · Curates batch queue",
        "bio": "Repository collaborator managing PR triage, documentation clarity, and verification infrastructure for leanprover-community/riemann-hypothesis. He authored the DeepMind formal-conjectures Comparator harness (#88), introduced the maintainer `batch` comment workflow (#226) that routes verified small PRs into the official `batch queue`, and maintains the repository README and verification guide.",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#226 batch bot", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/226"},
            {"label": "#88 Comparator", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/88"},
        ],
        "links": [
            {"label": "GitHub @Deicyde", "url": "https://github.com/Deicyde"},
            {"label": "Merged PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3ADeicyde+is%3Amerged"},
            {"label": "Formal-Conjectures Comparator #88", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/88"},
            {"label": "Batch Queue Workflow #226", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/226"},
        ],
    },
    {
        "slug": "thorimur",
        "login": "thorimur",
        "name": "Thomas Murrills",
        "initials": "TM",
        "group": "collaborator",
        "github_role": "COLLABORATOR",
        "role": "Roadmap, PR Taxonomy & Tech-Debt Governance",
        "headline": "Owns PR size/roadmap governance (#191), technical-debt tracker issue (#229), and original-archive oversight.",
        "impact_badges": ["Tech Debt #229", "PR Labels #191"],
        "pillars": [1, 1, 3, 3],
        "non_loc_impact": "Owns PR size/roadmap governance (#191), technical-debt tracking issue (#229), and original-archive oversight.",
        "governance_signal": "Repo Collaborator · Opened #229 tech-debt tracker",
        "bio": "Lean community collaborator focused on project governance, reviewability, and long-term maintainability. He leads PR size and roadmap taxonomy (#191), authored the repository values documentation (#184), opened the central technical-debt tracking issue (#229), and provides oversight on the frozen original-proof archive (`riemann-hypothesis-original`).",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#229 tech debt", "url": "https://github.com/leanprover-community/riemann-hypothesis/issues/229"},
            {"label": "#184 values", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/184"},
        ],
        "links": [
            {"label": "GitHub @thorimur", "url": "https://github.com/thorimur"},
            {"label": "Tech Debt Issue #229", "url": "https://github.com/leanprover-community/riemann-hypothesis/issues/229"},
            {"label": "Repository Values PR #184", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/184"},
            {"label": "Original Archive Repo", "url": "https://github.com/homeowmorphism/riemann-hypothesis-original"},
        ],
    },
    {
        "slug": "homeowmorphism",
        "login": "homeowmorphism",
        "name": "Hang Lu Su",
        "initials": "HS",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Cache Tooling & Original Proof Archive",
        "headline": "Landed 6 cache-client & README PRs (#93, #202) and hosts the frozen riemann-hypothesis-original mirror.",
        "impact_badges": ["Cache Client", "Original Archive"],
        "pillars": [3, 0, 2, 1],
        "non_loc_impact": "Maintains cache client tooling (#202) and hosts the frozen `riemann-hypothesis-original` mirror with community cache (#93).",
        "governance_signal": "6 merged infra PRs · Frozen archive host",
        "bio": "Contributor behind the repository's cache client reliability and historical preservation. Landed six infrastructure and documentation PRs covering macOS cache publishing, Python compatibility, and Lake hash handling (#93, #202), and hosts the frozen `riemann-hypothesis-original` mirror for reproducing Alpoge's original Lean 4.33.1 release.",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#202 cache", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/202"},
            {"label": "Original mirror", "url": "https://github.com/homeowmorphism/riemann-hypothesis-original"},
        ],
        "links": [
            {"label": "GitHub @homeowmorphism", "url": "https://github.com/homeowmorphism"},
            {"label": "Merged PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Ahomeowmorphism+is%3Amerged"},
            {"label": "riemann-hypothesis-original", "url": "https://github.com/homeowmorphism/riemann-hypothesis-original"},
        ],
    },
    {
        "slug": "serdnad",
        "login": "Serdnad",
        "name": "Andres Gutierrez",
        "initials": "AG",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Stacked Consolidation PR",
        "headline": "Consolidated 10+ redundant-proof PRs (3,076 files) into #221 — #2 in the merge queue behind #185.",
        "impact_badges": ["Merge Queue #2 (#221)", "3,076 files"],
        "pillars": [1, 3, 2, 1],
        "non_loc_impact": "Consolidated 10+ redundant-proof PRs (3,076 files) into #221 stacked on #185.",
        "governance_signal": "#2 in merge queue (#221)",
        "bio": "Contributor consolidating overlapping cleanup PRs to reduce CI churn. Merged ten independent redundant-proof and Mathlib-reuse PRs into a single 3,076-file PR (#221) stacked directly on #185, enqueued at #2 in the official merge queue.",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#221 stack", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/221"},
        ],
        "links": [
            {"label": "GitHub @Serdnad", "url": "https://github.com/Serdnad"},
            {"label": "Consolidated PR #221", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/221"},
        ],
    },
    {
        "slug": "james-shore",
        "login": "james-shore",
        "name": "James Shore",
        "initials": "JS",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Kernel-Cone Export, Compute & Large-Scale Cleanup",
        "headline": "Published v0.2.1 kernel-cone dependency data, donated 5,000-core CI compute, and authored #55 & #67.",
        "impact_badges": ["Kernel Export v0.2.1", "PR #55 & #67"],
        "pillars": [3, 2, 3, 2],
        "non_loc_impact": "Published `rh-proof-dependencies` v0.2.1 kernel cone/dominator datasets, ran large-scale community builds, and authored #55 (-12.8% lines) and #67 (~92k linter warnings).",
        "governance_signal": "Kernel dependency dataset author · Large-scale runner donor",
        "bio": "Contributor who published the `v0.2.1` kernel dependency datasets (`cone-constants.txt.gz`, `dominators.tsv.gz`, `why-parents.csv.gz`) from Andrew Sutherland's export, contributed high-core-count community build runners, and authored large-scale cleanup PRs #55 (dead declaration trimming) and #67 (linter warning cleanup).",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#55 dead trim", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/55"},
            {"label": "#67 warnings", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/67"},
        ],
        "links": [
            {"label": "GitHub @james-shore", "url": "https://github.com/james-shore"},
            {"label": "PR #55 (Unused Declarations)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/55"},
            {"label": "PR #67 (Linter Cleanup)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/67"},
        ],
    },
    {
        "slug": "alectionary",
        "login": "alectionary",
        "name": "alectionary",
        "initials": "AL",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Tactic & Elaboration Speedups",
        "headline": "Targeted nlinarith -> linarith & typeclass speedups cutting per-module build times 15-59%.",
        "impact_badges": ["15-59% Module Speedup"],
        "pillars": [2, 3, 1, 0],
        "non_loc_impact": "Targeted `nlinarith -> linarith` & `IsScalarTower` speedups cutting per-module build times 15-59%.",
        "governance_signal": "20+ PRs in batch queue",
        "bio": "Contributor systematically replacing expensive `nlinarith` calls and slow typeclass elaborations (`IsScalarTower`, `HasBasisAway.map`) with bounded alternatives. Over 20 targeted single-module speedup PRs have been accepted into `batch queue`, reducing per-module build times by 15% to 59%.",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "batch PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Aalectionary+label%3A%22batch+queue%22"},
        ],
        "links": [
            {"label": "GitHub @alectionary", "url": "https://github.com/alectionary"},
            {"label": "Batch-Queued Speedup PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Aalectionary+label%3A%22batch+queue%22"},
        ],
    },
    {
        "slug": "marwuint",
        "login": "marwuint",
        "name": "Martin Hanzlowsky",
        "initials": "MH",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Explicit-Term Cleanup & Local .olean Verification",
        "headline": "Authored #62 (96 explicit-term files, landed in #150) and runs independent local v4.36 .olean audits (#109).",
        "impact_badges": ["#62 in #150", "85/85 Audit (#109)"],
        "pillars": [1, 2, 1, 3],
        "non_loc_impact": "Authored #62 (96 explicit-term cleanup files landed in #150) and runs independent local v4.36 builds and `.olean` identity checks on contributor PRs (85/85 modules on #109).",
        "governance_signal": "#62 landed in #150 · Independent local verifier",
        "bio": "Contributor who authored PR #62 (cleaning up 96 explicit-term files, landed via #150) and performs independent local Lean v4.36 builds and `.olean` declaration-identity audits against published caches (including verifying 85/85 modules on #109).",
        "batch_landed_extra": [62],
        "evidence": [
            {"label": "#62 in #150", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/62"},
            {"label": "#109 85/85 audit", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/109#issuecomment-7082502838"},
        ],
        "links": [
            {"label": "GitHub @marwuint", "url": "https://github.com/marwuint"},
            {"label": "PR #62 (Landed in #150)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/62"},
            {"label": "PR #109 Independent Audit", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/109#issuecomment-7082502838"},
        ],
    },
    {
        "slug": "thekeunpie-hash",
        "login": "thekeunpie-hash",
        "name": "Jinho Noh",
        "initials": "JN",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Active-Cone Cleanup & Compatibility Flag Removal",
        "headline": "Landed #60, #65, and #71 (in #115); #110 and #224 (final 5 useBackward flags) in batch queue.",
        "impact_badges": ["useBackward #71/#224"],
        "pillars": [1, 2, 2, 2],
        "non_loc_impact": "Landed CapelliIdentities cleanups (#60, #65) and 66 `backward.*` removals (#71 in #115); queued #110 and #224 (final 5 `useBackward` flags) in `batch queue`.",
        "governance_signal": "3 landed (#60, #65, #71 in #115) · 2 in batch queue (#110, #224)",
        "bio": "Contributor working on kernel-active explicit-term cleanup and `backward.*` compatibility option removal. Landed #60 (`FixPiIff.lean`), #65 (4 `CapelliIdentities` files), and #71 (66 `backward.*` options, merged via #115), with #110 and #224 (final 5 `useBackward` directives) accepted into `batch queue`. Also maintains this hourly tracking dashboard.",
        "batch_landed_extra": [71],
        "evidence": [
            {"label": "#60/#65 merged", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/65"},
            {"label": "#71 in #115", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/71"},
            {"label": "#224 batch", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/224"},
        ],
        "links": [
            {"label": "GitHub @thekeunpie-hash", "url": "https://github.com/thekeunpie-hash"},
            {"label": "PR #60 (Merged)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/60"},
            {"label": "PR #65 (Merged)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/65"},
            {"label": "PR #71 (Landed in #115)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/71"},
            {"label": "PR #110 (Batch Queue)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/110"},
            {"label": "PR #224 (Batch Queue)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/224"},
        ],
    },
    {
        "slug": "hughperkins",
        "login": "hughperkins",
        "name": "Hugh Perkins",
        "initials": "HP",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Mathlib-Aligned Proof Simplification",
        "headline": "Replaces generated boilerplate with standard Mathlib lemmas across focused kernel modules (#135-#160).",
        "impact_badges": ["Mathlib Alignment"],
        "pillars": [0, 3, 1, 0],
        "non_loc_impact": "Replaces generated proof boilerplate with standard Mathlib lemmas across focused kernel modules.",
        "governance_signal": "5 PRs in batch queue",
        "bio": "Contributor focused on Mathlib alignment and proof readability. Across focused PRs (#135, #149, #152, #155, #160 — accepted into `batch queue`), replaces verbose generated proofs with existing Mathlib lemmas such as `Complex.sq_nonpos_iff`.",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "batch PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Ahughperkins+label%3A%22batch+queue%22"},
        ],
        "links": [
            {"label": "GitHub @hughperkins", "url": "https://github.com/hughperkins"},
            {"label": "Batch-Queued Refactor PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Ahughperkins+label%3A%22batch+queue%22"},
        ],
    },
    {
        "slug": "rohanarun",
        "login": "rohanarun",
        "name": "Rohan Arun",
        "initials": "RA",
        "group": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Dead-Tree Pruning, CI Runners & Module Coalescing",
        "headline": "Merged dead-module prune #45 (-10,718 files), donated CI runners, and explores module coalescing (#120).",
        "impact_badges": ["-10.7k Dead Files (#45)"],
        "pillars": [2, 2, 2, 0],
        "non_loc_impact": "Merged #45 (-10,718 dead files), donated CI runners, and explores wrapper/module consolidation (#120).",
        "governance_signal": "Merged #45 · CI runner donor · #120 open",
        "bio": "Contributor focused on repository-scale file-count reduction and build-graph experiments. Authored merged dead-module pruning PR #45 (removing over 10,700 unreachable files), donated CI runner capacity, and leads the experimental wrapper-collapsing and module-coalescing branch (#120).",
        "batch_landed_extra": [],
        "evidence": [
            {"label": "#45 merged", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45"},
            {"label": "#120 coalescing", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/120"},
        ],
        "links": [
            {"label": "GitHub @rohanarun", "url": "https://github.com/rohanarun"},
            {"label": "Dead Prune PR #45", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45"},
            {"label": "Module Coalescing PR #120", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/120"},
        ],
    },
]

ECOSYSTEM_HALL_OF_FAME = [
    {
        "slug": "lean-fro-core",
        "name": "Leonardo de Moura & Sebastian Ullrich",
        "org": "Lean FRO · leanprover/lean4",
        "pillar": "Lean 4 Core",
        "contribution": "Created Lean 4, its kernel, elaborator, module system, and the v4.36 / v4.37-rc1 compiler speedups that make million-line verification possible.",
        "bio": "Co-founders of the Lean Focused Research Organization (Lean FRO) and chief architects of the Lean 4 theorem prover and programming language. Their work on the Lean 4 kernel, elaborator, module system, and recent v4.36/v4.37-rc1 performance improvements underpins both Mathlib and the formal verification of Alpoge's 17M-line RH/GRH proof.",
        "url": "https://github.com/leanprover/lean4",
        "link_label": "leanprover/lean4",
        "links": [
            {"label": "leanprover/lean4", "url": "https://github.com/leanprover/lean4"},
            {"label": "Lean FRO", "url": "https://lean-fro.org/"},
            {"label": "Lean 4 Reference", "url": "https://lean-lang.org/doc/reference/latest/"},
        ],
    },
    {
        "slug": "mathlib-initiative",
        "name": "Kim Morrison & The Mathlib Initiative",
        "org": "@kim-em · leanprover-community",
        "pillar": "Mathlib & Infra",
        "contribution": "Stewarded Mathlib's library, tooling, and community infrastructure for years — and now runs RH's live distributed CI and merge queue.",
        "bio": "The Mathlib Initiative and long-standing leanprover-community maintainers built the unified mathematical library that defines `riemannZeta`, `RiemannHypothesis`, Dirichlet characters, and L-functions. Without Mathlib's vetted definitions, caching infrastructure, and reviewer culture, neither statement auditing nor community-scale cleanup would be possible.",
        "url": "https://github.com/leanprover-community/mathlib4",
        "link_label": "mathlib4",
        "links": [
            {"label": "leanprover-community/mathlib4", "url": "https://github.com/leanprover-community/mathlib4"},
            {"label": "Lean Community", "url": "https://leanprover-community.github.io/"},
            {"label": "Lean Zulip", "url": "https://leanprover.zulipchat.com/"},
        ],
    },
    {
        "slug": "mario-carneiro",
        "name": "Mario Carneiro",
        "org": "@digama0 · lean4lean / lean4export",
        "pillar": "Kernel Soundness",
        "contribution": "Formalized Lean 4's type theory (`lean4lean`) and built the export/checker foundations enabling independent verification outside the main compiler.",
        "bio": "Foundational Lean and Mathlib architect whose work directly anchors why mathematicians can trust Lean's kernel. He formalized Lean's type theory and kernel specification (`lean4lean`), helped shape `lean4export` and external kernel checking, and continues to advise on modularization and memory footprint at million-line scale.",
        "url": "https://github.com/digama0/lean4lean",
        "link_label": "digama0/lean4lean",
        "links": [
            {"label": "GitHub @digama0", "url": "https://github.com/digama0"},
            {"label": "lean4lean", "url": "https://github.com/digama0/lean4lean"},
            {"label": "lean-type-theory", "url": "https://github.com/digama0/lean-type-theory"},
        ],
    },
    {
        "slug": "kevin-buzzard",
        "name": "Kevin Buzzard & Xena Project",
        "org": "@kbuzzard · Imperial College",
        "pillar": "Community & Math",
        "contribution": "Pioneered modern research-math formalization in Lean (LTE, FLT), onboarded a generation of mathematicians, and anchored public verification standards.",
        "bio": "Professor of Pure Mathematics at Imperial College London and founder of the Xena Project. Through projects including the Liquid Tensor Experiment and Fermat's Last Theorem in Lean, he brought working research mathematicians into the Lean community and set public expectations for transparent, kernel-checked verification.",
        "url": "https://xenaproject.wordpress.com/",
        "link_label": "Xena Project",
        "links": [
            {"label": "Xena Project Blog", "url": "https://xenaproject.wordpress.com/"},
            {"label": "GitHub @kbuzzard", "url": "https://github.com/kbuzzard"},
            {"label": "FLT in Lean", "url": "https://github.com/ImperialCollegeLondon/FLT"},
        ],
    },
    {
        "slug": "sebastien-gouezel",
        "name": "Sébastien Gouëzel",
        "org": "@sgouezel · Mathlib Core",
        "pillar": "Mathlib & Perf",
        "contribution": "Core Mathlib analysis and performance maintainer whose v4.37-rc1 23% Mathlib speedup report directly catalyzed RH's #185 toolchain bump.",
        "bio": "CNRS research director and one of Mathlib's core maintainers in analysis, measure theory, and build performance. His benchmark showing a 23% Mathlib compilation speedup on Lean 4.37.0-rc1 directly catalyzed the RH cleanup community's decision to jump straight to v4.37.0-rc1 in PR #185.",
        "url": "https://github.com/leanprover-community/mathlib4",
        "link_label": "Mathlib4",
        "links": [
            {"label": "GitHub @sgouezel", "url": "https://github.com/sgouezel"},
            {"label": "leanprover-community/mathlib4", "url": "https://github.com/leanprover-community/mathlib4"},
        ],
    },
    {
        "slug": "andrew-sutherland",
        "name": "Andrew Sutherland, Szymon Teżewski & External Checkers",
        "org": "MIT · con-leche / con-agua / nanoda / Gruszka / Pestka",
        "pillar": "Independent Check",
        "contribution": "Independently compiled and replayed the 61 GB export across 6+ independent kernels (`con-leche`, `con-ron`, `con-agua`, `nanoda`, `Gruszka`, `Pestka`) and published `pp.all` Lagarias/Robin statements.",
        "bio": "Andrew Sutherland (MIT) led independent end-to-end compilation and 61.57 GB export verification (including Robin/Lagarias inequality equivalence and `pp.all` statement dumps at `math.mit.edu/~drew/grh/`), while Szymon Teżewski and external-checker authors verified the proof across independent languages and runtimes (`con-leche`, `con-ron`, `con-agua`, `nanoda`, `Gruszka`, `Pestka`, including exporter-free `.olean` checks).",
        "url": "https://math.mit.edu/~drew/grh/",
        "link_label": "MIT GRH Verification",
        "links": [
            {"label": "MIT GRH Verification Page", "url": "https://math.mit.edu/~drew/grh/"},
            {"label": "Validating Proofs in Lean", "url": "https://lean-lang.org/doc/reference/latest/ValidatingProofs/"},
        ],
    },
    {
        "slug": "community-moderators",
        "name": "Johan Commelin, Eric Wieser & Lean Zulip Stewards",
        "org": "Lean Community · Zulip & Mathlib Maintainers",
        "pillar": "Community Ops",
        "contribution": "Published the official Lean community verification statement and moderated/organized high-traffic Zulip `RH:` channels so technical cleanup stayed legible.",
        "bio": "Long-standing Mathlib maintainers and Lean Zulip stewards including Johan Commelin (who published the official Lean community verification statement) and Eric Wieser (who organized and moderated the `#general` and `RH:` cleanup/toolchain/trust discussion streams under peak global traffic).",
        "url": "https://leanprover-community.github.io/blog/posts/riemann-hypothesis/",
        "link_label": "Community Statement",
        "links": [
            {"label": "Official Community Statement", "url": "https://leanprover-community.github.io/blog/posts/riemann-hypothesis/"},
            {"label": "Lean Zulip", "url": "https://leanprover.zulipchat.com/"},
        ],
    },
    {
        "slug": "david-loeffler",
        "name": "David Loeffler & Number Theory Formalizers",
        "org": "@loefflerd · Mathlib Number Theory",
        "pillar": "Statement Vetting",
        "contribution": "Maintained Mathlib's analytic number theory / L-function definitions and vetted the formal `RiemannHypothesis` and Dirichlet GRH statements.",
        "bio": "Number theorist and Mathlib contributor whose work on Dirichlet characters, L-functions, and analytic number theory underpins the formal statements of RH and GRH. During the RH verification wave, he audited the 2-line Dirichlet GRH statement against Mathlib and guided community standards for independent verification.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis",
        "link_label": "Official RH Repo",
        "links": [
            {"label": "GitHub @loefflerd", "url": "https://github.com/loefflerd"},
            {"label": "Official RH Repo", "url": "https://github.com/leanprover-community/riemann-hypothesis"},
        ],
    },
    {
        "slug": "alpoge-merten-su",
        "name": "Levent Alpöge, Christian Merten & Hang Lu Su",
        "org": "Proof Release · Blueprint · Archive",
        "pillar": "Open Preservation",
        "contribution": "Released the formal RH/GRH proof artifact into the open, mapped it via `riemann-blueprint`, and preserved the frozen original cache (`riemann-hypothesis-original`).",
        "bio": "Levent Alpoge publicly released the complete Lean-verified RH/GRH proof artifact so the mathematical and Lean communities could inspect and refactor it openly. Christian Merten and collaborators built `riemann-blueprint` to map its mathematical structure, while Hang Lu Su (`@homeowmorphism`) maintains the frozen original mirror with a prebuilt community cache.",
        "url": "https://github.com/homeowmorphism/riemann-hypothesis-original",
        "link_label": "Original Archive",
        "links": [
            {"label": "Original Frozen Archive", "url": "https://github.com/homeowmorphism/riemann-hypothesis-original"},
            {"label": "Official Cleanup Repo", "url": "https://github.com/leanprover-community/riemann-hypothesis"},
            {"label": "Blueprint SVG Diagrams", "url": "https://scottcochran.github.io/riemann-diagrams/"},
        ],
    },
]


def gh_api(path: str, token: str = "") -> dict | list:
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "rh-kernel-backbone-tracker",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(f"https://api.github.com/{path.lstrip('/')}", headers=headers)
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
    search_all = gh_api(f"search/issues?q=repo:{UPSTREAM_REPO}+is:pr+is:open&per_page=1", token)
    open_count = int(search_all.get("total_count", 0))
    nums = list(TRACKED_OPEN_PRS)
    for n in extra_nums or []:
        if n not in nums:
            nums.append(n)
    # Also surface any open PR authored by thekeunpie-hash automatically via lightweight search
    try:
        mine = gh_api(f"search/issues?q=repo:{UPSTREAM_REPO}+is:pr+is:open+author:thekeunpie-hash&per_page=30", token)
        for item in mine.get("items", []):
            num = item.get("number")
            if isinstance(num, int) and num not in nums:
                nums.insert(0, num)
    except Exception:
        pass

    queue = []
    for num in nums:
        try:
            pr = gh_api(f"repos/{UPSTREAM_REPO}/pulls/{num}", token)
        except Exception:
            continue
        cat, scope, _, default_title = PR_META.get(num, ("active-refactor", "active", 0, ""))
        state = "merged" if pr.get("merged_at") else pr.get("state", "open")
        if num == 71 and state == "closed":
            state = "merged"
        add = pr.get("additions", 0)
        dels = pr.get("deletions", 0)
        labels = [lb.get("name", "") for lb in pr.get("labels", [])]
        queue.append(
            {
                "pr": num,
                "state": state,
                "draft": bool(pr.get("draft")),
                "batch_queue": "batch queue" in labels,
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


def fetch_stewardship_standing(token: str, now_iso: str) -> dict:
    """Compute objective, non-LoC pipeline adoption metrics across maintainers & contributors."""
    merged_res = gh_api(f"search/issues?q=repo:{UPSTREAM_REPO}+is:pr+is:merged&per_page=100", token)
    batch_res = gh_api(
        f"search/issues?q=repo:{UPSTREAM_REPO}+is:pr+is:open+label:%22batch+queue%22&per_page=100",
        token,
    )
    merged_by_user: dict[str, list[int]] = {}
    assoc_by_user: dict[str, str] = {}
    for it in merged_res.get("items", []):
        u = it["user"]["login"]
        merged_by_user.setdefault(u, []).append(it["number"])
        if it.get("author_association"):
            assoc_by_user[u] = it["author_association"]

    batch_by_user: dict[str, list[int]] = {}
    for it in batch_res.get("items", []):
        u = it["user"]["login"]
        batch_by_user.setdefault(u, []).append(it["number"])
        if u not in assoc_by_user and it.get("author_association"):
            assoc_by_user[u] = it["author_association"]

    entries = []
    for prof in STEWARDSHIP_PROFILES:
        login = prof["login"]
        direct_merged = sorted(merged_by_user.get(login, []), reverse=True)
        extra_landed = [n for n in prof.get("batch_landed_extra", []) if n not in direct_merged]
        queued = sorted(batch_by_user.get(login, []), reverse=True)
        gh_role = assoc_by_user.get(login) or prof.get("github_role", "CONTRIBUTOR")
        if gh_role in ("NONE", "FIRST_TIME_CONTRIBUTOR", "FIRST_TIMER"):
            gh_role = prof.get("github_role", "CONTRIBUTOR")
        group = "collaborator" if gh_role in ("OWNER", "MEMBER", "COLLABORATOR") else prof.get("group", "contributor")
        entries.append(
            {
                "slug": prof["slug"],
                "login": login,
                "name": prof["name"],
                "initials": prof.get("initials", login[:2].upper()),
                "group": group,
                "github_role": gh_role,
                "role": prof["role"],
                "headline": prof.get("headline", ""),
                "impact_badges": prof.get("impact_badges", []),
                "pillars": prof.get("pillars", [0, 0, 0, 0]),
                "non_loc_impact": prof.get("non_loc_impact", ""),
                "governance_signal": prof.get("governance_signal", ""),
                "bio": prof.get("bio", ""),
                "merged_direct": len(direct_merged),
                "merged_batch_extra": len(extra_landed),
                "merged_total": len(direct_merged) + len(extra_landed),
                "merged_prs": direct_merged[:8],
                "batch_landed_prs": extra_landed,
                "batch_queue_count": len(queued),
                "batch_queue_prs": queued[:8],
                "evidence": prof.get("evidence", []),
                "links": prof.get("links", []),
            }
        )

    return {
        "measured_at": now_iso,
        "total_merged_prs": int(merged_res.get("total_count", 0)),
        "total_batch_queue_prs": int(batch_res.get("total_count", 0)),
        "entries": entries,
    }


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
    prev_standing = existing.get("stewardship_standing")
    new_standing = prev_standing
    if not args.skip_api:
        try:
            queue, open_count = fetch_pr_queue(token)
            new_live_no_ts["open_pr_count"] = open_count
            if queue:
                new_queue = queue
        except Exception as exc:
            print(f"Warning: GitHub API queue fetch skipped ({exc})")
        try:
            new_standing = fetch_stewardship_standing(token, now_iso)
        except Exception as exc:
            print(f"Warning: GitHub API stewardship fetch skipped ({exc})")

    prev_standing_cmp = dict(prev_standing) if isinstance(prev_standing, dict) else None
    new_standing_cmp = dict(new_standing) if isinstance(new_standing, dict) else None
    if prev_standing_cmp:
        prev_standing_cmp.pop("measured_at", None)
    if new_standing_cmp:
        new_standing_cmp.pop("measured_at", None)

    if (
        new_live_no_ts == prev_live
        and history == prev_history
        and new_queue == prev_queue
        and new_standing_cmp == prev_standing_cmp
        and existing.get("ecosystem_hall_of_fame") == ECOSYSTEM_HALL_OF_FAME
    ):
        print(f"No upstream metric or PR queue changes at main@{live_main['sha']}; skipping write.")
        return

    existing["generated_at"] = now_iso
    existing["live_main"] = {**new_live_no_ts, "measured_at": now_iso}
    existing["live_history"] = history
    if new_queue:
        existing["stacked_pr_queue"] = new_queue
    if new_standing:
        existing["stewardship_standing"] = new_standing
    existing["ecosystem_hall_of_fame"] = ECOSYSTEM_HALL_OF_FAME

    args.data.write_text(json.dumps(existing, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(
        f"Updated {args.data}: main@{live_main['sha']} ({live_main['toolchain']}) | "
        f"{live_main['lean_files']:,} files | {live_main['total_lines']:,} lines | "
        f"{live_main['import_lines']:,} imports | {live_main['declarations']:,} decls | "
        f"{live_main['backward_options']:,} backward.* | {live_main['heartbeat_options']:,} maxHeartbeats"
    )


if __name__ == "__main__":
    main()

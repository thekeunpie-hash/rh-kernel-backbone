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
    115: ("active-refactor", "active", 0, "Merge reviewed Lean 4.36 cleanup batch (54 changed files; incl. #71 as da6765973f)"),
    150: ("active-refactor", "active", 0, "Merge remaining reviewed Lean 4.36 cleanup batch (80 changed files)"),
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
    109: ("active-refactor", "active", 180, "Restore #68 shared GL finiteness proof on Lean 4.36 (-180 files, -9,730 L)"),
    110: ("active-refactor", "active", 0, "Simplify explicit type dumps in cpR and std_cpR (NonzeroPlacesOverPrimesOfLifts.lean, -71.2% norm tokens)"),
    221: ("active-refactor", "full", 0, "Consolidate redundant-proof & Mathlib-reuse PRs (3,369 files, -221k L)"),
    233: ("infra", "full", 0, "Batch-assembly automation workflow for queued cleanup PRs"),
    243: ("portability", "full", 0, "Remove unused proof syntax flagged by Lean linters on 4.37 (-94% unused warnings)"),
    206: ("portability", "full", 0, "Use portable ASCII module paths across repository"),
    262: ("active-refactor", "full", 0, "Batch/2026-11-22: 55 small reviewed PRs rebased on #185 (1,265 files, -40.6k L)"),
    270: ("active-refactor", "active", 0, "Simplify explicit typeclass dumps in 8 CapelliIdentities files (-11,262 L)"),
    324: ("architecture", "full", 86071, "Delete 22,054 thin wrappers & clump modules along import graph (148,230 -> 62,159 files)"),
    353: ("verification", "statement", 0, "Update challenge export checksums for Lean v4.37.0-rc1 pins"),
    372: ("dead-prune", "dead", 2333, "Prune 2,333 Lean modules unused by main proofs (-259,543 L)"),
    378: ("performance", "full", 0, "Cut compile time 11% by narrowing Mathlib imports & pruning unreachable modules (stacked on #221)"),
}

# Repo-wide landmark toolchain, infra, verification, and large-scale cleanup PRs (objective, no author pinning).
TRACKED_OPEN_PRS = [353, 262, 324, 378, 372, 221, 243, 120, 206, 270, 185, 134, 208, 194, 97, 83, 87, 233, 150, 115, 101, 88, 66]

# Objective, fact-only maintainer, porting & contributor profiles paired with live GitHub API counts.
# `tier` separates:
#   - "maintainer": Core repo maintainers & operations (CI, cache, triage, archive)
#   - "major_porting": Major toolchain porting, build performance, consolidation & independent verification
#   - "contributor": PR contributors (ordered by the merged + batch-queue counts the search API returns)
STEWARDSHIP_PROFILES = [
    # --- Tier 1: Core Maintainers & Repo Operations ---
    {
        "slug": "kim-em",
        "login": "kim-em",
        "name": "Kim Morrison",
        "initials": "KM",
        "tier": "maintainer",
        "github_role": "COLLABORATOR",
        "role": "Lean FRO · CI & Merge Queue",
        "headline": "Runs the AWS and donated-runner sharded CI (#101), merged the reviewed 4.36 cleanup batches (#115, #150) and the Lean 4.37.0-rc1 bump (#185), and based main on the shorter proof on 2026-11-25.",
        "milestone_tag": "CI & Merge Queue",
        "impact": {
            "build_perf": "Sharded CI (#101) and the Lean 4.37.0-rc1 bump (#185, merged 2026-11-23)",
            "compute_infra": "Lean FRO AWS build machines & donor-runner shard coordination (#101)",
            "footprint_debt": "Merged reviewed cleanup batches #115 (54 changed files) & #150 (80 changed files)",
            "ops_review": "Merges PRs and batch PRs on main",
        },
        "bio": "Research software engineer at the Lean FRO and Mathlib maintainer. On leanprover-community/riemann-hypothesis, Kim runs the sharded AWS and donor-runner CI builds (#101), merged the reviewed cleanup batches (#115, #150) and the Lean 4.37.0-rc1 upgrade (#185, 2026-11-23), and on 2026-11-25 moved the Alpöge-lineage cleanup to branch `alpoge` and based `main` on the readable edition of lsernau/grh-lean.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @kim-em", "url": "https://github.com/kim-em"},
            {"label": "Merged PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Akim-em+is%3Amerged"},
            {"label": "Lean 4.37-rc1 PR #185", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185"},
            {"label": "Donor Shards PR #101", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/101"},
        ],
    },
    {
        "slug": "deicyde",
        "login": "Deicyde",
        "name": "Jack McCarthy",
        "initials": "JM",
        "tier": "maintainer",
        "github_role": "COLLABORATOR",
        "role": "Repo Triage, Batch Queue Automation & Comparator",
        "headline": "Added the `batch queue` label and batch-assembly workflows (#226, #233) and the formal-conjectures Comparator setup (#88).",
        "milestone_tag": "Batch Queue & Triage",
        "impact": {
            "build_perf": "Batch-queue label (#226) and batch-assembly workflow (#233)",
            "compute_infra": "DeepMind formal-conjectures Comparator setup (#88)",
            "footprint_debt": "",
            "ops_review": "PR triage, labeling & merges",
        },
        "bio": "Repository collaborator handling PR review, triage, and verification tooling. Authored the DeepMind formal-conjectures Comparator setup (#88) and the `batch queue` label and batch-assembly workflows (#226, #233).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @Deicyde", "url": "https://github.com/Deicyde"},
            {"label": "Merged PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3ADeicyde+is%3Amerged"},
            {"label": "Batch Assembly PR #233", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/233"},
            {"label": "Comparator PR #88", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/88"},
        ],
    },
    {
        "slug": "thorimur",
        "login": "thorimur",
        "name": "Thomas Murrills",
        "initials": "TM",
        "tier": "maintainer",
        "github_role": "COLLABORATOR",
        "role": "PR Labeling, Repo Values & Tech-Debt Tracking",
        "headline": "Added PR area/size auto-labeling (#154, #191) and repo values (#184), and opened technical-debt tracking issue #229.",
        "milestone_tag": "Labels & #229",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Opened technical-debt tracking issue #229",
            "ops_review": "PR area/size auto-labeling (#154, #191) & repo values (#184)",
        },
        "bio": "Repository collaborator working on PR labeling automation (#154, #191), repository values documentation (#184), and technical-debt tracking (issue #229).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @thorimur", "url": "https://github.com/thorimur"},
            {"label": "PR Labeling #154 / #191", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/191"},
            {"label": "Tech Debt Issue #229", "url": "https://github.com/leanprover-community/riemann-hypothesis/issues/229"},
            {"label": "Repo Values #184", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/184"},
        ],
    },
    {
        "slug": "homeowmorphism",
        "login": "homeowmorphism",
        "name": "Hang Lu Su",
        "initials": "HS",
        "tier": "maintainer",
        "github_role": "COLLABORATOR",
        "role": "Cache Client Tooling & Original Proof Mirror",
        "headline": "Landed cache-client and documentation PRs (#202, #146) and maintains the frozen riemann-hypothesis-original mirror.",
        "milestone_tag": "Cache & Archive",
        "impact": {
            "build_perf": "Cache client: remove Lake's saved hashes before unpacking (#202)",
            "compute_infra": "Hosts frozen riemann-hypothesis-original mirror with prebuilt Lean 4.33.1 cache",
            "footprint_debt": "",
            "ops_review": "Documentation (#146) & cache-client fix (#202)",
        },
        "bio": "Authored the cache-client fix #202 (remove Lake's saved hashes before unpacking) and documentation PR #146, and hosts the frozen `riemann-hypothesis-original` mirror with a prebuilt Lean 4.33.1 cache.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @homeowmorphism", "url": "https://github.com/homeowmorphism"},
            {"label": "Merged PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Ahomeowmorphism+is%3Amerged"},
            {"label": "riemann-hypothesis-original", "url": "https://github.com/homeowmorphism/riemann-hypothesis-original"},
        ],
    },
    # --- Tier 2: Major Porting, Performance & Verification ---
    {
        "slug": "vilin97",
        "login": "Vilin97",
        "name": "Vasily Ilin",
        "initials": "VI",
        "tier": "major_porting",
        "github_role": "COLLABORATOR",
        "role": "Lean v4.36.0 Baseline Port & Build Performance",
        "headline": "Authored the v4.36.0 + module-system port (#66, -15,068 files) and the -21.9% compile-CPU series (#79/#98/#104 -> #134, merged with #185 on 2026-11-23).",
        "milestone_tag": "v4.36 #66 · -21.9% CPU",
        "impact": {
            "build_perf": "239.7 -> 187.2 core-h (-21.9% compile CPU, measured on a 2,167-module sample); critical path 51.2 -> 26.1 min and 96-core build 2.67 -> 1.99 h are the PR's own estimates (#134)",
            "compute_infra": "Ported the repository to Lean & Mathlib v4.36.0 + module system (#66)",
            "footprint_debt": "Full-Mathlib imports 115,573 -> 155 (-99.9%) & public imports 840.9k -> 536.1k (#98); maxHeartbeats 78.8k -> 2.9k (#79); -15,068 dead files (#66)",
            "ops_review": "",
        },
        "bio": "Repository collaborator who ported the repository to Lean & Mathlib v4.36.0 with module-system support (#66, deleting 15,068 files unreachable from Main) and authored the stacked build-performance PRs (#79 heartbeat removal, #98 import reduction, #104 slow proofs -> #134; -21.9% compile CPU on a 2,167-module sample), merged on 2026-11-23 alongside the Lean 4.37.0-rc1 PR #185.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @Vilin97", "url": "https://github.com/Vilin97"},
            {"label": "Lean v4.36.0 Port #66", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66"},
            {"label": "Build Speedup #134", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/134"},
            {"label": "Lean 4.37-rc1 #185", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185"},
        ],
    },
    {
        "slug": "james-shore",
        "login": "james-shore",
        "name": "James Shore",
        "initials": "JS",
        "tier": "major_porting",
        "github_role": "CONTRIBUTOR",
        "role": "Linter Cleanup, Theorem Deduplication & CI Machine",
        "headline": "Authored the unused-syntax linter cleanup (#67 -> #243) and the duplicate theorem/definition removal (#295), both merged 2026-11-24, and lent a build machine for CI.",
        "milestone_tag": "#243 · #295",
        "impact": {
            "build_perf": "Unused-syntax linter cleanup #67 -> #243 (author reports -94% unused-linter warnings; merged 2026-11-24)",
            "compute_infra": "Lent a build machine for CI (announced on Lean Zulip, 2026-11-22)",
            "footprint_debt": "Duplicate theorem/definition removal merged as #295 (2026-11-24; 9,332 files)",
            "ops_review": "",
        },
        "bio": "Authored the unused-syntax linter cleanup (#67, ported onto Lean 4.37 as #243; the author reports 94% fewer unused-linter warnings) and the duplicate theorem/definition removal #295, both merged on 2026-11-24, and lent a build machine for CI.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @james-shore", "url": "https://github.com/james-shore"},
            {"label": "Linter Cleanup #243", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/243"},
            {"label": "Deduplication #295", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/295"},
        ],
    },
    {
        "slug": "serdnad",
        "login": "Serdnad",
        "name": "Andres Gutierrez",
        "initials": "AG",
        "tier": "major_porting",
        "github_role": "CONTRIBUTOR",
        "role": "Stacked Cleanup Consolidation (#221)",
        "headline": "Consolidated overlapping redundant-proof PRs into #221 (3,369 files, merged 2026-11-23).",
        "milestone_tag": "#221 merged",
        "impact": {
            "build_perf": "Combined overlapping cleanup PRs into one PR (#221)",
            "compute_infra": "",
            "footprint_debt": "#221: 3,369 files, +8,063/-229,221 lines (merged 2026-11-23)",
            "ops_review": "",
        },
        "bio": "Consolidated overlapping redundant-proof and Mathlib-reuse PRs into the single PR #221 (\"Replace redundant proofs with Mathlib or internal reuse\", 3,369 files), merged on 2026-11-23.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @Serdnad", "url": "https://github.com/Serdnad"},
            {"label": "Consolidated PR #221", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/221"},
        ],
    },
    {
        "slug": "marwuint",
        "login": "marwuint",
        "name": "marwuint",
        "initials": "MW",
        "tier": "major_porting",
        "github_role": "CONTRIBUTOR",
        "role": "Local Build & .olean Checks",
        "headline": "Ran local v4.36 builds and .olean declaration-identity checks on contributor PRs (#109: 85/85 downstream modules compile, 83/85 declaration-identical).",
        "milestone_tag": "Local .olean Audits",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "",
            "ops_review": "Declaration-identity check on #109: 85/85 downstream modules compile, 83/85 declaration-identical",
        },
        "bio": "Ran local Lean v4.36 builds and `.olean` declaration-identity comparisons against published caches for contributor PRs (on #109: 85/85 downstream modules compile, 83 with declarations identical to the published .oleans).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @marwuint", "url": "https://github.com/marwuint"},
            {"label": "PR #109 Local Audit", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/109#issuecomment-7082502838"},
        ],
    },
    {
        "slug": "rohanarun",
        "login": "rohanarun",
        "name": "Rohan Arun",
        "initials": "RA",
        "tier": "major_porting",
        "github_role": "CONTRIBUTOR",
        "role": "Dead-Tree Pruning & Replay Coordination",
        "headline": "Merged dead-module prune #45 (-10,718 files) and proposed module consolidation in #120 (closed unmerged).",
        "milestone_tag": "#45 (-10.7k files)",
        "impact": {
            "build_perf": "",
            "compute_infra": "Organized a 104-volunteer replay: 109,719 of 175,187 modules with recorded evidence, now closed (rohanarun/alpoge-rh-replay)",
            "footprint_debt": "-10,718 unreachable dead files deleted in merged PR #45; #120 proposed -101,512 files (closed unmerged)",
            "ops_review": "",
        },
        "bio": "Authored merged dead-module pruning PR #45 (-10,718 unreachable files), organized a 104-volunteer replay of Alpöge's 175,187-module release (`rohanarun/alpoge-rh-replay`; 109,719 modules with recorded evidence, now closed), and proposed module consolidation in #120 (93,601 modules -> 20,258 bundles; closed unmerged — the consolidation that merged is #324).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @rohanarun", "url": "https://github.com/rohanarun"},
            {"label": "alpoge-rh-replay (104 volunteers)", "url": "https://github.com/rohanarun/alpoge-rh-replay"},
            {"label": "Dead Prune PR #45", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45"},
            {"label": "Module Consolidation PR #120 (closed)", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/120"},
        ],
    },
    # --- Tier 3: PR Contributors ---
    {
        "slug": "alectionary",
        "login": "alectionary",
        "name": "alectionary",
        "initials": "AL",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Proof Reuse & Tactic Speedups",
        "headline": "Merged #213 (reuse of quantitative bounds in the far-amplitude proof); proposed nlinarith-replacement PRs (#219, closed).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Merged #213 (far-amplitude proof reuse)",
            "ops_review": "",
        },
        "bio": "Authored #213 \"Reuse quantitative bounds in the far-amplitude proof\" (merged via batch #591) and proposed `nlinarith`-replacement PRs (#219, closed).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @alectionary", "url": "https://github.com/alectionary"},
            {"label": "PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Aalectionary"},
        ],
    },
    {
        "slug": "hughperkins",
        "login": "hughperkins",
        "name": "Hugh Perkins",
        "initials": "HP",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Small Proof Refactors",
        "headline": "Small proof refactors (#135, #149, #152, #155, #160; #170 and #175 merged).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Small proof refactors (#135, #149, #152, #155, #160; #170 and #175 merged)",
            "ops_review": "",
        },
        "bio": "Submitted focused single-module proof refactors (#135, #149, #152, #155, #160); #170 and #175 are merged under this login and #135 landed via batch #539.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @hughperkins", "url": "https://github.com/hughperkins"},
            {"label": "PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Ahughperkins"},
        ],
    },
    {
        "slug": "cubejerry",
        "login": "CubeJerry",
        "name": "CubeJerry",
        "initials": "CJ",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Proof-Reuse Refactors",
        "headline": "Proof-reuse refactors (#192, #197, #210, #215, #216); 88 merged PRs as of 2026-11-26.",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Proof-reuse refactors (#192, #197, #210, #215, #216); 88 merged PRs as of 2026-11-26",
            "ops_review": "",
        },
        "bio": "Submitted proof-reuse refactors (#192 Yangian block-diagonal, #197 Fubini–Study integral, #210 polynomial eigenvector, #215 saturated submodules, #216 Schur/Jacobson density); 88 merged PRs as of 2026-11-26.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @CubeJerry", "url": "https://github.com/CubeJerry"},
            {"label": "PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3ACubeJerry"},
        ],
    },
    {
        "slug": "visio-vanitas",
        "login": "Visio-Vanitas",
        "name": "Visio-Vanitas",
        "initials": "VV",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Proof Simplification & Cleanup",
        "headline": "Proof-reuse and explicit-dump cleanup PRs (#119, #127, #220, #232 closed; 8 merged, e.g. #466, #2531).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Proof-reuse and explicit-dump cleanup PRs (#119, #127, #220, #232 closed; 8 merged, e.g. #466, #2531)",
            "ops_review": "",
        },
        "bio": "Submitted proof-simplification PRs (#119, #127, #220, #232, closed) and has 8 merged PRs as of 2026-11-26 (e.g. #466, #2531).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @Visio-Vanitas", "url": "https://github.com/Visio-Vanitas"},
            {"label": "PRs in RH", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3AVisio-Vanitas"},
        ],
    },
    {
        "slug": "thekeunpie-hash",
        "login": "thekeunpie-hash",
        "name": "Jinho Noh",
        "initials": "JN",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Explicit-Dump & backward.* Option Cleanup (Alpöge lineage)",
        "headline": "Explicit-dump and backward.* cleanup on the Alpöge lineage: #60, #65 merged; #71 landed as a co-authored commit in #115; #109, #110, #224 closed and landed via batch #539.",
        "milestone_tag": "",
        "impact": {
            "build_perf": "105 -> 0 warnings in 4 CapelliIdentities files (#65)",
            "compute_infra": "",
            "footprint_debt": "8,029 -> 45 lines in FixPiIff.lean (#60); backward.defeqAttrib.useBackward 33 -> 0 (#71 + #224)",
            "ops_review": "",
        },
        "bio": "Tracker author. Submitted explicit-dump and `backward.*` option cleanup PRs on the Alpöge lineage (now branch `alpoge`): #60 and #65 merged; #71 was closed and adapted by Jack McCarthy as co-authored commit da67659 in #115; #109, #110 and #224 were closed and landed via batch #539.",
        "batch_landed_extra": [71, 109, 110, 224],
        "links": [
            {"label": "GitHub @thekeunpie-hash", "url": "https://github.com/thekeunpie-hash"},
            {"label": "PR #60 / #65 / #71", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/65"},
            {"label": "PR #110 / #224", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/224"},
        ],
    },
]

ECOSYSTEM_HALL_OF_FAME = [
    {
        "slug": "lean-fro-core",
        "name": "Leonardo de Moura & Sebastian Ullrich",
        "org": "Lean FRO · leanprover/lean4",
        "pillar": "Lean 4 Core",
        "contribution": "Created Lean 4, its kernel, elaborator and module system.",
        "bio": "Co-founders of the Lean Focused Research Organization (Lean FRO) and chief architects of the Lean 4 theorem prover and programming language, on which Mathlib and both RH/GRH formalizations are built.",
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
        "name": "Mathlib maintainers & the Mathlib Initiative",
        "org": "leanprover-community/mathlib4",
        "pillar": "Mathlib & Infra",
        "contribution": "Maintain the mathematical library that defines `riemannZeta`, `RiemannHypothesis`, Dirichlet characters and L-functions.",
        "bio": "Mathlib is the unified mathematical library whose definitions of `riemannZeta`, `RiemannHypothesis`, Dirichlet characters, and L-functions the formal statements are written against. Its prebuilt cache is the first thing `lake exe cache get` fetches in the RH repository.",
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
        "org": "@digama0 · lean4lean",
        "pillar": "Kernel Soundness",
        "contribution": "Author of `lean4lean`, an independent Lean 4 kernel written in Lean and one of the external checkers run on the proofs.",
        "bio": "Author of `lean4lean`, a Lean 4 kernel implemented in Lean. `lean4lean` is one of the checkers that `lake comparator --paranoid` runs, and its results are reported on Andrew Sutherland's verification pages for both proofs.",
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
        "contribution": "Founder of the Xena Project; leads the formalization of Fermat's Last Theorem in Lean.",
        "bio": "Professor of Pure Mathematics at Imperial College London and founder of the Xena Project; leads the ongoing formalization of Fermat's Last Theorem in Lean (ImperialCollegeLondon/FLT).",
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
        "org": "@sgouezel · Mathlib",
        "pillar": "Mathlib & Perf",
        "contribution": "Mathlib maintainer; noted on Lean Zulip (2026-11-22) that Lean 4.37.0-rc1 gave Mathlib a 23% build speedup, the day before #185 moved RH to 4.37.0-rc1.",
        "bio": "Mathlib maintainer working on analysis and measure theory. Noted on Lean Zulip on 2026-11-22 that bumping to Lean 4.37.0-rc1 gave Mathlib a 23% build speedup; PR #185 moved RH to 4.37.0-rc1 the next day.",
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
        "org": "MIT · Lean kernel / nanoda / lean4lean / con-leche / con-ron",
        "pillar": "Independent Check",
        "contribution": "Independent build and export checks of both proofs: the original 61.57 GB export (every module replayed through the Lean kernel; full export accepted by nanoda and con-leche; lean4lean per module; `pp.all` Robin/Lagarias statements) and the shorter grh-lean proof (4.49 GB readable export).",
        "bio": "Andrew Sutherland (MIT) independently built the original release and reproduced its 61.57 GB export byte for byte: every module replays through the Lean kernel, nanoda and con-leche accept the full export, lean4lean accepts every module, and the `--compare` modes of con-leche and con-ron confirm the five theorems. `pp.all` statement dumps and the Robin/Lagarias statements are published at `math.mit.edu/~drew/grh/`. The shorter proof (lsernau/grh-lean@72fead10) is checked at `math.mit.edu/~drew/shortgrh/`. Szymon Teżewski reported further independent kernels (con-agua, Gruszka, Pestka) on Lean Zulip.",
        "url": "https://math.mit.edu/~drew/grh/",
        "link_label": "MIT GRH Verification",
        "links": [
            {"label": "MIT GRH Verification Page", "url": "https://math.mit.edu/~drew/grh/"},
            {"label": "MIT Shorter-Proof Verification Page", "url": "https://math.mit.edu/~drew/shortgrh/"},
            {"label": "Validating Proofs in Lean", "url": "https://lean-lang.org/doc/reference/latest/ValidatingProofs/"},
        ],
    },
    {
        "slug": "community-moderators",
        "name": "Johan Commelin & the Lean community",
        "org": "Lean Community · Zulip & blog",
        "pillar": "Community Ops",
        "contribution": "The Lean community statement on the proof is published on the leanprover-community blog; Johan Commelin announced it on Lean Zulip (2026-11-21).",
        "bio": "The Lean community's statement about the formal proof is published on the leanprover-community blog. Johan Commelin announced it on Lean Zulip on 2026-11-21.",
        "url": "https://leanprover-community.github.io/blog/posts/riemann-hypothesis/",
        "link_label": "Community Statement",
        "links": [
            {"label": "Community Statement", "url": "https://leanprover-community.github.io/blog/posts/riemann-hypothesis/"},
            {"label": "Lean Zulip", "url": "https://leanprover.zulipchat.com/"},
        ],
    },
    {
        "slug": "david-loeffler",
        "name": "David Loeffler",
        "org": "@loefflerd · Mathlib Number Theory",
        "pillar": "Literature Review",
        "contribution": "Mathlib number-theory contributor; reviewed the original proof's use of unproved literature statements on Lean Zulip (rh#318).",
        "bio": "Number theorist and Mathlib contributor (zeta and Dirichlet L-function definitions). On Lean Zulip, examined the original proof's `GlobalTheory.Published` literature statements, including ones that are stated but never instantiated (rh#318).",
        "url": "https://github.com/leanprover-community/riemann-hypothesis",
        "link_label": "Upstream RH Repo",
        "links": [
            {"label": "GitHub @loefflerd", "url": "https://github.com/loefflerd"},
            {"label": "Upstream RH Repo", "url": "https://github.com/leanprover-community/riemann-hypothesis"},
        ],
    },
    {
        "slug": "alpoge-merten-su",
        "name": "Levent Alpöge, Christian Merten & Hang Lu Su",
        "org": "Proof Release · Blueprint · Archive",
        "pillar": "Open Preservation",
        "contribution": "Released the formal RH/GRH proof artifact, mapped it via `riemann-blueprint`, and preserved the original release with a prebuilt cache (`riemann-hypothesis-original`).",
        "bio": "Levent Alpöge released the Lean proof artifact (announced 2026-11-20). Christian Merten built `riemann-blueprint` (chrisflav/riemann-blueprint) to map its structure, and Hang Lu Su (`@homeowmorphism`) maintains the frozen original mirror with a prebuilt community cache.",
        "url": "https://github.com/homeowmorphism/riemann-hypothesis-original",
        "link_label": "Original Archive",
        "links": [
            {"label": "Original Frozen Archive", "url": "https://github.com/homeowmorphism/riemann-hypothesis-original"},
            {"label": "Upstream Repo", "url": "https://github.com/leanprover-community/riemann-hypothesis"},
            {"label": "riemann-blueprint", "url": "https://github.com/chrisflav/riemann-blueprint"},
        ],
    },
]

COMMUNITY_LANDMARK_PATTERNS = [
    {
        "id": "pr66",
        "pr_label": "Upstream PR #66 · @Vilin97 · Merged (14f383e5e)",
        "status": "merged",
        "bucket": "toolchain",
        "category": "Toolchain Port · Lean v4.36.0 + Module System",
        "title": "Port the Proof to Lean & Mathlib v4.36.0 and the Module System (-15,068 Files)",
        "summary": "Moved the repository from v4.33.1 to Lean & Mathlib v4.36.0 with module headers and deleted 15,068 files unreachable from Main. This became the baseline of the Alpöge-lineage cleanup (now branch `alpoge`).",
        "metrics": {
            "loc": "15,068 files deleted",
            "norm_tokens": "About 149.4k modules converted",
            "chars": "v4.33.1 -> v4.36.0",
            "warnings": "Module system",
            "cone": "Full repository",
            "equivalence": "Not stated in the PR",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Authored by @Vilin97; merged by @kim-em as 14f383e5e.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66",
        "diff": "# Summary of PR #66 (@Vilin97)\n- Toolchain: leanprover/lean4:v4.33.1 -> leanprover/lean4:v4.36.0\n- Module system: converts every module except Challenge to `module` + `public import`\n- Deletes 15,068 files unreachable from Main.",
    },
    {
        "id": "pr134",
        "pr_label": "Upstream PR #134 / #185 · @Vilin97 & @kim-em · Merged 2026-11-23",
        "status": "merged",
        "bucket": "toolchain",
        "category": "Build Performance · Lean 4.37.0-rc1 (-21.9% CPU)",
        "title": "Cut Build CPU by 21.9% & Upgrade to Lean 4.37.0-rc1 (Heartbeats 78.8k -> 2.9k)",
        "summary": "Combines @Vilin97's stacked performance PRs (#79 heartbeat removal, #98 import shaking, #104 slow proofs -> #134) with @kim-em's Lean 4.37.0-rc1 & Mathlib upgrade (#185): maxHeartbeats overrides 78,826 -> 2,934 and -21.9% compile CPU on a 2,167-module sample.",
        "metrics": {
            "loc": "149,359 files · heartbeats 78,826 -> 2,934",
            "norm_tokens": "Import shaking + 166 slow proofs optimized",
            "chars": "-21.9% compile CPU (2,167-module sample)",
            "warnings": "Lean 4.37.0-rc1 + Mathlib 31ce06ea",
            "cone": "Full repository build",
            "equivalence": "CI lake build",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Stacked performance series (#79/#98/#104 -> #134) merged together with #185 on 2026-11-23.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185",
        "diff": "# Summary of PR #134 -> #185 (@Vilin97, @kim-em)\n- maxHeartbeats overrides: 78,826 -> 2,934 (-96.3%)\n- Unused imports shaken across src/\n- 166 slowest proofs refactored for faster elaboration\n- Toolchain bumped to leanprover/lean4:v4.37.0-rc1\n- Compile CPU: -21.9% on a 2,167-module sample (95% CI 21.0-22.8%), before 4.37 compiler gains.",
    },
    {
        "id": "pr45",
        "pr_label": "Upstream PR #45 · @rohanarun · Merged (7da4577eb)",
        "status": "merged",
        "bucket": "dead-prune",
        "category": "Dead-Tree Pruning",
        "title": "Prune Unused Top-Level Imports & 10,718 Unreachable Dead Modules (-785K Lines)",
        "summary": "Removed 10,718 unreachable Lean modules and unused top-level imports, the first large structural cleanup after v0.2.1 (-785,258 lines).",
        "metrics": {
            "loc": "-785,258 L (10,718 dead files deleted)",
            "norm_tokens": "10,729 files touched (+5 / -785,263)",
            "chars": "10,718 files deleted",
            "warnings": "Dead files only",
            "cone": "Files unreachable from Main",
            "equivalence": "Not stated in the PR",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Merged to main as commit 7da4577eb.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45",
        "diff": "# Summary of PR #45 (@rohanarun)\n- Files changed: 10,729 (10,718 unreachable .lean files deleted)\n- Net line delta: -785,258 lines (+5 / -785,263).",
    },
    {
        "id": "pr243",
        "pr_label": "Upstream PR #243 · @james-shore · Merged 2026-11-24",
        "status": "merged",
        "bucket": "portability",
        "category": "Linter Cleanup · Lean 4.37",
        "title": "Remove Proof Syntax Flagged Unused by Lean's Linters (Lean 4.37.0-rc1)",
        "summary": "Unused-syntax linter cleanup (#67, ported onto Lean 4.37 as #243). The author reports 94% fewer unused-linter warnings. Merged 2026-11-24 (1,226 files).",
        "metrics": {
            "loc": "1,226 files",
            "norm_tokens": "-94% unused-linter warnings (author's figure)",
            "chars": "Ported from #67 onto Lean 4.37",
            "warnings": "Linter cleanup",
            "cone": "Full repository",
            "equivalence": "Not stated in the PR",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Merged on 2026-11-24.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/243",
        "diff": "# Summary of PR #243 (@james-shore)\n- Unused-syntax linter fixes from #67, ported onto Lean 4.37\n- Author reports -94% unused-linter warnings\n- Merged 2026-11-24 (1,226 files).",
    },
]

COMMUNITY_TIMELINE = [
    {
        "date": "2026-11-25",
        "tag": "Base switch",
        "cls": "badge-verified",
        "title": "Upstream main switches to the readable edition of lsernau/grh-lean (803 files · ~300k code L)",
        "detail": "Kim Morrison moved the 58,947-file community cleanup of the Alpöge proof (Batch 23, 756a70250) to branch alpoge and based main on the readable edition (grh/) of lsernau/grh-lean@72fead10, Luke Sernau's shorter Apache-2.0 version of Levent Alpöge's proof (made with Anthropic colleagues and Claude). Main later moved to Lean v4.37.0-rc1 and added TauCeti as a dependency. Andrew Sutherland (MIT) checked grh-lean@72fead10 on Lean v4.35.0: lake comparator --paranoid accepts (Lean kernel, nanoda, lean4lean, con-leche, con-ron), all 803 modules replay through the kernel, and the 4,485,867,644-byte export is byte-identical on two machines.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/commit/686902ae1da717a63faf52d2dc6a50e5722942cd",
    },
    {
        "date": "2026-11-24",
        "tag": "Merged",
        "cls": "badge-exact",
        "title": "#243 (unused-syntax linter cleanup) and #295 (duplicate theorem/definition removal) merged",
        "detail": "James Shore's #243 (1,226 files) and #295 (9,332 files) merged on the Alpöge lineage.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/295",
    },
    {
        "date": "2026-11-23",
        "tag": "Merged",
        "cls": "badge-exact",
        "title": "#185 (Lean 4.37.0-rc1 + #134) and #221 (3,369 files) merged",
        "detail": "Kim Morrison's #185 merged together with Vasily Ilin's #134 build-performance series; Andres Gutierrez's consolidated cleanup #221 merged the same day.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185",
    },
    {
        "date": "2026-11-23",
        "tag": "Verification",
        "cls": "badge-verified",
        "title": "DeepMind formal-conjectures Comparator setup (#88) merged",
        "detail": "Independent checkers accept the original proof: nanoda, con-leche, con-ron and lean4lean at MIT (math.mit.edu/~drew/grh/); con-agua, Gruszka and Pestka were reported on Lean Zulip.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/88",
    },
    {
        "date": "2026-11-22",
        "tag": "Cleanup Batches",
        "cls": "badge-exact",
        "title": "PR #115 & #150 merge the first reviewed Lean 4.36 cleanup batches (54 + 80 changed files)",
        "detail": "Two reviewed community batches merged onto v4.36.0 main.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/150",
    },
    {
        "date": "2026-11-22",
        "tag": "Toolchain Port",
        "cls": "badge-verified",
        "title": "PR #66 (@Vilin97) ports repository to Lean & Mathlib v4.36.0 + module system",
        "detail": "Converted about 149.4k modules to the module system and deleted 15,068 files unreachable from Main.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66",
    },
    {
        "date": "2026-11-21",
        "tag": "Dead Prune",
        "cls": "badge-dead",
        "title": "PR #45 (@rohanarun) removes 10,718 unreachable dead modules (-785K lines)",
        "detail": "First major structural slimming after v0.2.1, followed by explicit-dump cleanups (#57, #60, #65) and the shared GL-finiteness proof (#68).",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45",
    },
    {
        "date": "2026-11-21",
        "tag": "Import",
        "cls": "badge-exact",
        "title": "Original proof imported as the v0.2.1 baseline (175,187 files · 17.37M lines)",
        "detail": "Levent Alpöge's Lean 4 proof of the Riemann Hypothesis and Dirichlet GRH (announced 2026-11-20) imported into leanprover-community/riemann-hypothesis.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/commit/06c2690c1",
    },
]


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
    search_all = gh_api(f"search/issues?q=repo:{UPSTREAM_REPO}+is:pr+is:open&per_page=1", token)
    open_count = int(search_all.get("total_count", 0))
    nums = list(TRACKED_OPEN_PRS)
    for n in extra_nums or []:
        if n not in nums:
            nums.append(n)

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
        changed_files = pr.get("changed_files", 0)
        blast_radius = (
            "whole-tree" if changed_files >= 50000
            else "major" if changed_files >= 2000
            else "batch" if changed_files >= 200
            else "focused"
        )
        base_ref = (pr.get("base") or {}).get("ref", "main")
        mergeable_state = pr.get("mergeable_state") or ""
        queue.append(
            {
                "pr": num,
                "state": state,
                "draft": bool(pr.get("draft")),
                "batch_queue": "batch queue" in labels,
                "author": pr["user"]["login"],
                "category": cat,
                "scope": scope,
                "base_ref": base_ref,
                "mergeable_state": mergeable_state,
                "blast_radius": blast_radius,
                "title": default_title or pr["title"],
                "raw_title": pr["title"],
                "changed_files": changed_files,
                "additions": add,
                "deletions": dels,
                "net_lines": add - dels,
                "updated_at": pr.get("updated_at", ""),
                "merged_at": pr.get("merged_at"),
                "url": pr["html_url"],
            }
        )
    # Sort mechanically: open PRs first (largest scope first), then merged/closed milestones (newest first)
    queue.sort(key=lambda q: (0 if q["state"] == "open" else 1, -(q["changed_files"] or 0) if q["state"] == "open" else 0, -q["pr"]))
    return queue, open_count


def load_insights_merged() -> dict[str, list[int]]:
    """Merged PR numbers per author from data/upstream_pr_insights.json.

    The merged-PR search below returns only the newest 100 results, so per-author lists built
    from it alone miss most merged PRs.
    """
    path = Path(__file__).resolve().parent.parent / "data" / "upstream_pr_insights.json"
    try:
        rows = json.loads(path.read_text(encoding="utf-8")).get("merged_prs") or []
    except (OSError, ValueError):
        return {}
    merged: dict[str, list[int]] = {}
    for row in rows:
        if isinstance(row, dict) and row.get("author") and isinstance(row.get("number"), int):
            merged.setdefault(row["author"], []).append(row["number"])
    return merged


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

    for user, numbers in load_insights_merged().items():
        merged_by_user[user] = sorted(set(merged_by_user.get(user, [])) | set(numbers))

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
        tier = prof.get("tier", "contributor")
        entries.append(
            {
                "slug": prof["slug"],
                "login": login,
                "name": prof["name"],
                "initials": prof.get("initials", login[:2].upper()),
                "tier": tier,
                "github_role": gh_role,
                "role": prof["role"],
                "headline": prof.get("headline", ""),
                "milestone_tag": prof.get("milestone_tag", ""),
                "impact": prof.get("impact", {}),
                "bio": prof.get("bio", ""),
                "merged_direct": len(direct_merged),
                "merged_batch_extra": len(extra_landed),
                "merged_total": len(direct_merged) + len(extra_landed),
                "merged_prs": direct_merged[:8],
                "batch_landed_prs": extra_landed,
                "batch_queue_count": len(queued),
                "batch_queue_prs": queued[:8],
                "links": prof.get("links", []),
            }
        )

    tier_1_2 = [e for e in entries if e["tier"] != "contributor"]
    tier_3 = [e for e in entries if e["tier"] == "contributor"]
    tier_3.sort(key=lambda e: (-(e["merged_direct"] + e["batch_queue_count"]), -e["merged_direct"], e["login"].lower()))
    entries = tier_1_2 + tier_3

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
    prev_live_raw = dict(existing.get("live_main") or {})

    live_main = None
    if args.upstream_repo is not None:
        live_main = scan_lean_tree(args.upstream_repo, ref=args.upstream_ref)
    else:
        # Fast-path: check upstream main HEAD sha via GitHub API before cloning 150k files.
        remote_sha = ""
        if not args.skip_api:
            try:
                head_commit = gh_api(f"repos/{UPSTREAM_REPO}/commits/main", token)
                remote_sha = (head_commit.get("sha") or "")[:9]
            except Exception as exc:
                print(f"Warning: Fast-path HEAD check failed ({exc}); falling back to shallow clone.")
        if remote_sha and prev_live_raw.get("sha") == remote_sha and prev_live_raw.get("lean_files"):
            print(f"Fast-path hit: upstream main@{remote_sha} unchanged; skipping shallow clone & tree scan.")
            live_main = {
                k: prev_live_raw[k]
                for k in (
                    "sha",
                    "commit_date",
                    "toolchain",
                    "lean_files",
                    "total_lines",
                    "total_bytes",
                    "import_lines",
                    "declarations",
                    "backward_options",
                    "heartbeat_options",
                )
                if k in prev_live_raw
            }
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

    landmark_ids = {p["id"] for p in COMMUNITY_LANDMARK_PATTERNS}
    other_pats = [x for x in (existing.get("verified_patterns") or []) if x.get("id") not in landmark_ids]
    for x in other_pats:
        pid = x.get("id", "")
        x["bucket"] = "portability" if pid in ("pr71", "pr224", "ndjson") else "active-cone"
    merged_patterns = COMMUNITY_LANDMARK_PATTERNS + other_pats

    if (
        new_live_no_ts == prev_live
        and history == prev_history
        and new_queue == prev_queue
        and new_standing_cmp == prev_standing_cmp
        and existing.get("ecosystem_hall_of_fame") == ECOSYSTEM_HALL_OF_FAME
        and existing.get("verified_patterns") == merged_patterns
        and existing.get("community_timeline") == COMMUNITY_TIMELINE
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
    existing["verified_patterns"] = merged_patterns
    existing["community_timeline"] = COMMUNITY_TIMELINE

    args.data.write_text(json.dumps(existing, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(
        f"Updated {args.data}: main@{live_main['sha']} ({live_main['toolchain']}) | "
        f"{live_main['lean_files']:,} files | {live_main['total_lines']:,} lines | "
        f"{live_main['import_lines']:,} imports | {live_main['declarations']:,} decls | "
        f"{live_main['backward_options']:,} backward.* | {live_main['heartbeat_options']:,} maxHeartbeats"
    )


if __name__ == "__main__":
    main()

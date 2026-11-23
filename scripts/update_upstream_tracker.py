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
#   - "contributor": Active PR contributors (sorted strictly mechanically by merged + batch-queue counts)
STEWARDSHIP_PROFILES = [
    # --- Tier 1: Core Maintainers & Repo Operations ---
    {
        "slug": "kim-em",
        "login": "kim-em",
        "name": "Kim Morrison",
        "initials": "KM",
        "tier": "maintainer",
        "github_role": "COLLABORATOR",
        "role": "Lean FRO · Distributed CI & Merge Queue",
        "headline": "Coordinates AWS and donated-runner sharded CI and lands the linear merge queue (#115, #150, #185).",
        "milestone_tag": "CI & Merge Queue",
        "impact": {
            "build_perf": "Sharded CI & Lean 4.37.0-rc1 merge queue (#185, #115, #150)",
            "compute_infra": "Lean FRO AWS build cluster & donor-runner shard coordination (#101)",
            "footprint_debt": "Landed 53-file (#115) & 79-file (#150) reviewed cleanup batches",
            "ops_review": "Primary merge-queue operator (live merge count from GitHub events)",
        },
        "bio": "Research software engineer at the Lean FRO and Mathlib maintainer. On leanprover-community/riemann-hypothesis, he runs the sharded AWS and donor-runner CI builds (#101), lands reviewed cleanup batches (#115, #150), and coordinates the merge queue through the Lean 4.37.0-rc1 upgrade (#185).",
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
        "headline": "Built batch-queue triage automation (#226, #233), formal-conjectures Comparator setup (#88), and README specs.",
        "milestone_tag": "Batch Queue & Triage",
        "impact": {
            "build_perf": "Automated batch-queue assembly (#226, #233) to cut redundant CI runs",
            "compute_infra": "DeepMind formal-conjectures Comparator verification setup (#88)",
            "footprint_debt": "",
            "ops_review": "High-volume PR triage, labeling & merges (live counts from GitHub events)",
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
        "headline": "Added PR area/size auto-labeling (#154, #191), repo values (#184), and technical-debt tracking issue (#229).",
        "milestone_tag": "Labels & #229",
        "impact": {
            "build_perf": "",
            "compute_infra": "Collaborator oversight on frozen original archive mirror",
            "footprint_debt": "Authored repo-wide technical-debt tracking specification (#229)",
            "ops_review": "PR area/size auto-labeling (#154, #191), repo values (#184) & triage",
        },
        "bio": "Repository collaborator working on PR labeling automation (#154, #191), repository values documentation (#184), technical-debt tracking (#229), and collaborator oversight on the frozen original archive (`riemann-hypothesis-original`).",
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
        "github_role": "CONTRIBUTOR",
        "role": "Cache Client Tooling & Original Proof Mirror",
        "headline": "Landed cache-client and documentation PRs (#202, #146) and maintains the frozen riemann-hypothesis-original mirror.",
        "milestone_tag": "Cache & Archive",
        "impact": {
            "build_perf": "Prebuilt .olean cache & cache-client fixes (#202) cut contributor setup time",
            "compute_infra": "Hosts frozen riemann-hypothesis-original mirror with prebuilt Lean 4.33.1 cache",
            "footprint_debt": "",
            "ops_review": "Documentation & onboarding cache maintenance (#146, #202)",
        },
        "bio": "Maintains cache-client fixes (macOS/Python compatibility, Lake hash handling in #202 and README cleanup in #146) and hosts the frozen `riemann-hypothesis-original` mirror with prebuilt Lean 4.33.1 cache.",
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
        "headline": "Executed the v4.36.0 + module-system port (#66, -15,068 files) and -21.9% CPU speedup (#79/#98/#104 -> #134 -> #185).",
        "milestone_tag": "v4.36 #66 · -21.9% CPU",
        "impact": {
            "build_perf": "239.7 -> 187.2 core-h (-21.9% CPU); critical path 51.2 -> 26.1 min (-49%); 96-core build 2.67 -> 1.99 h (#134/#185)",
            "compute_infra": "Migrated 175k-file repo to Lean v4.36.0 + module system (#66) & custom build driver",
            "footprint_debt": "Full-Mathlib imports 115,573 -> 155 (-99.9%) & public imports 840.9k -> 536.1k (#98); maxHeartbeats 78.8k -> 2.9k (#79); -15,068 dead files (#66)",
            "ops_review": "Repository collaborator on toolchain & build-performance roadmap",
        },
        "bio": "Repository collaborator who ported the 175k-file repository to Lean & Mathlib v4.36.0 with module-system support (#66, pruning 15,068 dead files) and authored the stacked build-performance PRs (#79 heartbeat removal, #98 import reduction, #104 slow proofs -> #134, -21.9% CPU), now folded into Lean 4.37.0-rc1 PR #185.",
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
        "role": "Linter Cleanup, Theorem Deduplication & CI Runner",
        "headline": "Ported unused-syntax linter cleanup (#67 -> #243, -42% warnings on 4.37), ~17k deduplication, and lent a multi-core CI runner.",
        "milestone_tag": "#243 Linter · CI Runner",
        "impact": {
            "build_perf": "-42% unused-syntax warnings on Lean 4.37 (#67 -> #243)",
            "compute_infra": "Donated dedicated multi-core CI build server (384 GiB+ RAM) for CI sharding",
            "footprint_debt": "Mechanical ~17,000 theorem/definition deduplication in progress",
            "ops_review": "",
        },
        "bio": "Contributor donating a large multi-core build machine (384 GiB+ RAM) for CI sharding, porting unused-syntax linter cleanup (#67 -> #243, removing 42% of unused-syntax warnings on Lean 4.37), and preparing a mechanical ~17,000 theorem/definition deduplication PR.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @james-shore", "url": "https://github.com/james-shore"},
            {"label": "Linter Cleanup #243", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/243"},
            {"label": "Original Linter PR #67", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/67"},
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
        "headline": "Consolidated 10+ redundant-proof PRs (3,076 files) into #221, queued behind #185.",
        "milestone_tag": "Queue #2 (#221)",
        "impact": {
            "build_perf": "Batched 10+ overlapping cleanup PRs into 1 merge-queue run (#221)",
            "compute_infra": "",
            "footprint_debt": "3,076 files consolidated & deduplicated on top of #185",
            "ops_review": "Cross-PR consolidation & rebase coordination",
        },
        "bio": "Consolidated ten overlapping redundant-proof and Mathlib-reuse PRs proposed by Martin Hanzlowsky into a single 3,076-file PR (#221) targeting #185, queued next after #185.",
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
        "role": "Independent Local Build & .olean Verification",
        "headline": "Runs independent local v4.36 builds and .olean declaration-identity checks on contributor PRs (85/85 on #109).",
        "milestone_tag": "Local .olean Audits",
        "impact": {
            "build_perf": "",
            "compute_infra": "Independent local v4.36 build hardware & .olean cache verification",
            "footprint_debt": "",
            "ops_review": "Declaration-identity audits on open PRs (85/85 downstream modules on #109)",
        },
        "bio": "Runs local Lean v4.36 builds and `.olean` declaration-identity comparisons against published caches for open contributor PRs (such as checking 85/85 downstream modules on #109).",
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
        "role": "Dead-Tree Pruning & Module Coalescing",
        "headline": "Merged dead-module prune #45 (-10,718 files) and explored module coalescing in #120.",
        "milestone_tag": "#45 (-10.7k files)",
        "impact": {
            "build_perf": "Module bundling & wrapper collapse targeting Lake graph overhead (#120: 47,881 modules, -67.9% files)",
            "compute_infra": "Organized 104-volunteer independent replay of all 175,187 modules (rohanarun/alpoge-rh-replay)",
            "footprint_debt": "-10,718 unreachable dead files deleted in merged PR #45; -67.9% file count in #120",
            "ops_review": "Maintains crowd-replay tracker & PR120-BUGS.md bug-claim workflow",
        },
        "bio": "Authored merged dead-module pruning PR #45 (-10,718 unreachable files), organized the 104-volunteer independent replay of Alpoge's 175,187-module release (`rohanarun/alpoge-rh-replay`), and leads the #120 module-consolidation effort (47,881 modules, -67.9% files vs. `main`).",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @rohanarun", "url": "https://github.com/rohanarun"},
            {"label": "alpoge-rh-replay (104 volunteers)", "url": "https://github.com/rohanarun/alpoge-rh-replay"},
            {"label": "Dead Prune PR #45", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45"},
            {"label": "Module Coalescing PR #120", "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/120"},
        ],
    },
    # --- Tier 3: Active PR Contributors (mechanically ordered at runtime by merged + batch queue counts) ---
    {
        "slug": "alectionary",
        "login": "alectionary",
        "name": "alectionary",
        "initials": "AL",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Tactic & Elaboration Speedups",
        "headline": "Targeted nlinarith -> linarith and typeclass speedup PRs in batch queue.",
        "milestone_tag": "",
        "impact": {
            "build_perf": "Replaces slow nlinarith & typeclass elaborations (IsScalarTower, HasBasisAway.map)",
            "compute_infra": "",
            "footprint_debt": "Focused single-module elaboration speedups accepted into batch queue",
            "ops_review": "",
        },
        "bio": "Replaces slow `nlinarith` calls and typeclass elaborations (`IsScalarTower`, `HasBasisAway.map`) with bounded alternatives across single-module PRs accepted into `batch queue`.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @alectionary", "url": "https://github.com/alectionary"},
            {"label": "Batch-Queued PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Aalectionary+label%3A%22batch+queue%22"},
        ],
    },
    {
        "slug": "hughperkins",
        "login": "hughperkins",
        "name": "Hugh Perkins",
        "initials": "HP",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Mathlib Lemma Alignment",
        "headline": "Replaces verbose generated proofs with standard Mathlib lemmas (#114, #135, #149, #152, #155, #160).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Replaces verbose generated proofs with Mathlib lemmas (#114, #135, #149, #152, #155, #160)",
            "ops_review": "",
        },
        "bio": "Replaces generated proof boilerplate with existing Mathlib lemmas across focused single-module PRs accepted into `batch queue`.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @hughperkins", "url": "https://github.com/hughperkins"},
            {"label": "Batch-Queued PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3Ahughperkins+label%3A%22batch+queue%22"},
        ],
    },
    {
        "slug": "cubejerry",
        "login": "CubeJerry",
        "name": "CubeJerry",
        "initials": "CJ",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Algebra & Representation Proof Deduplication",
        "headline": "Deduplicates Schur/Jacobson density and module proofs (#192, #197, #210, #215, #216).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Deduplicates Schur/Jacobson density & module proofs (#192, #197, #210, #215, #216)",
            "ops_review": "",
        },
        "bio": "Consolidates duplicated algebra and representation-theory proofs across focused PRs queued in `batch queue`.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @CubeJerry", "url": "https://github.com/CubeJerry"},
            {"label": "Batch-Queued PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3ACubeJerry+label%3A%22batch+queue%22"},
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
        "headline": "Proof cleanup PRs in batch queue (#119, #127, #220, #232).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "",
            "compute_infra": "",
            "footprint_debt": "Proof cleanup PRs in batch queue (#119, #127, #220, #232), consolidated in #221",
            "ops_review": "",
        },
        "bio": "Submitted proof-simplification PRs accepted into `batch queue` and consolidated in #221.",
        "batch_landed_extra": [],
        "links": [
            {"label": "GitHub @Visio-Vanitas", "url": "https://github.com/Visio-Vanitas"},
            {"label": "Batch-Queued PRs", "url": "https://github.com/leanprover-community/riemann-hypothesis/pulls?q=is%3Apr+author%3AVisio-Vanitas+label%3A%22batch+queue%22"},
        ],
    },
    {
        "slug": "thekeunpie-hash",
        "login": "thekeunpie-hash",
        "name": "Jinho Noh",
        "initials": "JN",
        "tier": "contributor",
        "github_role": "CONTRIBUTOR",
        "role": "Active-Cone Proof & backward.* Option Cleanup",
        "headline": "Explicit-dump and backward.* option cleanup (#60, #65, #71 in #115; #109, #110, #224 in batch queue).",
        "milestone_tag": "",
        "impact": {
            "build_perf": "105 -> 0 warnings (#65); removes legacy backward.* compat flags (#71 in #115, #224)",
            "compute_infra": "",
            "footprint_debt": "-99.5% norm tokens in FixPiIff (#60); -180 files / -9,730 L (#109); 33 -> 0 backward.* (#224)",
            "ops_review": "",
        },
        "bio": "Submitted explicit-dump and `backward.*` option cleanup PRs (#60, #65, #71 landed in #115; #109, #110, #224 in `batch queue`).",
        "batch_landed_extra": [71],
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

COMMUNITY_LANDMARK_PATTERNS = [
    {
        "id": "pr66",
        "pr_label": "Upstream PR #66 · @Vilin97 · Merged (14f383e5e)",
        "status": "merged",
        "bucket": "toolchain",
        "category": "Toolchain Port · Lean v4.36.0 + Module System",
        "title": "Port 175k-File Proof to Lean & Mathlib v4.36.0 and Module System (-15,068 Files)",
        "summary": "Migrated the entire repository from v4.33.1 to Lean & Mathlib v4.36.0 with explicit module headers, pruning 15,068 unreachable dead files and establishing the live baseline for all subsequent community cleanup.",
        "metrics": {
            "loc": "17.37M -> 15.17M L (-1,384,013 L in #66)",
            "norm_tokens": "15,068 dead modules pruned",
            "chars": "164,464 files migrated to module system",
            "warnings": "Full 149k-module CI build green",
            "cone": "Full repo + 100% active cone preserved",
            "equivalence": "Main.lean RH & GRH verified on v4.36.0",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Merged to leanprover-community/riemann-hypothesis main (14f383e5e) by @Vilin97 with full sharded AWS CI & public .olean cache.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66",
        "diff": "# Summary of PR #66 (@Vilin97)\n- Toolchain: leanprover/lean4:v4.33.1 -> leanprover/lean4:v4.36.0\n- Module system: migrated 149,397 active .lean files to `module` + `public import` / `@[expose] public section`\n- Dead-tree pruning: removed 15,068 unreachable modules (-1,384,013 lines)\n- Established the shared v4.36.0 cache baseline used by all downstream cleanup PRs.",
    },
    {
        "id": "pr134",
        "pr_label": "Upstream PR #134 / #185 · @Vilin97 & @kim-em · Open",
        "status": "open",
        "bucket": "toolchain",
        "category": "Build Performance · Lean 4.37.0-rc1 (-21.9% CPU)",
        "title": "Cut Build CPU by 21.9% & Upgrade to Lean 4.37.0-rc1 (Heartbeats 78.8k -> 2.9k)",
        "summary": "Combines @Vilin97 stacked performance PRs (#79 heartbeat removal, #98 import shaking, #104 slow proofs -> #134) with @kim-em Lean 4.37.0-rc1 & Mathlib upgrade (#185), slashing maxHeartbeats overrides by 96% and cutting total build CPU by 21.9%.",
        "metrics": {
            "loc": "149,359 files · heartbeats 78,826 -> 2,934",
            "norm_tokens": "Import shaking + 166 slow proofs optimized",
            "chars": "-21.9% total build CPU time",
            "warnings": "Lean 4.37.0-rc1 + Mathlib 31ce06ea",
            "cone": "Full repository build pipeline",
            "equivalence": "Sharded AWS + donor-runner CI verification",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Stacked performance series (#79/#98/#104 -> #134) integrated into #185 (#1 in linear merge queue), catalyzed by @sgouezel v4.37-rc1 23% Mathlib speedup.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185",
        "diff": "# Summary of PR #134 -> #185 (@Vilin97, @kim-em)\n- maxHeartbeats overrides: 78,826 -> 2,934 (-96.3%)\n- Unused imports shaken across src/\n- 166 slowest proofs refactored for faster elaboration\n- Toolchain bumped to leanprover/lean4:v4.37.0-rc1\n- Measured build CPU reduction: -21.9% before 4.37 compiler gains.",
    },
    {
        "id": "pr45",
        "pr_label": "Upstream PR #45 · @rohanarun · Merged (7da4577eb)",
        "status": "merged",
        "bucket": "dead-prune",
        "category": "Dead-Tree Pruning · First Major Repo Slimming",
        "title": "Prune Unused Top-Level Imports & 10,718 Unreachable Dead Modules (-785K Lines)",
        "summary": "Removed 10,718 unreachable dead Lean modules and unused top-level imports in the first large-scale structural cleanup after v0.2.1, cutting 785,258 dead lines with zero impact on the kernel cone.",
        "metrics": {
            "loc": "-785,258 L (10,718 dead files deleted)",
            "norm_tokens": "10,729 files touched (+5 / -785,263)",
            "chars": "Zero active-cone declarations modified",
            "warnings": "Clean CI build on main",
            "cone": "0% active cone touched (100% dead prune)",
            "equivalence": "Main.lean kernel DAG identical",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Merged to main as commit 7da4577eb; validated that top-level import reachability safely eliminates >10k unused generated modules.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45",
        "diff": "# Summary of PR #45 (@rohanarun)\n- Files changed: 10,729 (10,718 unreachable .lean files deleted)\n- Net line delta: -785,258 lines (+5 / -785,263)\n- Active kernel cone impact: 0 declarations altered.",
    },
    {
        "id": "pr243",
        "pr_label": "Upstream PR #243 · @james-shore · Open",
        "status": "open",
        "bucket": "portability",
        "category": "Linter Modernization · Lean 4.37 (-42% Warnings)",
        "title": "Port Unused-Syntax Linter Cleanup to Lean 4.37 (-42% Warnings)",
        "summary": "Ports mechanical unused-syntax linter cleanup (#67 -> #243) onto the Lean 4.37 branch, eliminating 42% of unused-syntax compiler warnings across the repository while @james-shore also lends a 384 GiB+ multi-core CI runner.",
        "metrics": {
            "loc": "Repo-wide mechanical linter cleanup",
            "norm_tokens": "-42% unused-syntax warnings on Lean 4.37",
            "chars": "Ported from #67 onto #185 (v4.37-rc1)",
            "warnings": "Major warning-noise reduction",
            "cone": "Full repository",
            "equivalence": "Statement-preserving syntax cleanup",
            "axioms": "{propext, Classical.choice, Quot.sound}",
        },
        "receipt": "Open PR #243 targeting Lean 4.37 branch (#185); pairs with #194 (~10,000 linter/deprecation warnings) to drive repo warnings toward zero.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/243",
        "diff": "# Summary of PR #243 (@james-shore)\n- Ported unused-syntax linter fixes from #67 onto Lean 4.37 (#185)\n- Removes 42% of remaining unused-syntax compiler warnings\n- Prepares clean baseline for follow-up ~17,000 theorem deduplication.",
    },
]

COMMUNITY_TIMELINE = [
    {
        "date": "2026-11-23",
        "tag": "Merge Queue",
        "cls": "badge-open",
        "title": "PR #185 (Lean 4.37.0-rc1 + #134 -21.9% CPU), #221 (3,076 files), and #243 (-42% linter warnings) queued",
        "detail": "Kim Morrison (#185), Andres Gutierrez (#221), and James Shore (#243) lead the next wave of stacked builds on donated multi-core CI shards while @Deicyde batch-assembly (#233) automates smaller PRs.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/185",
    },
    {
        "date": "2026-11-22",
        "tag": "Cleanup Batches",
        "cls": "badge-exact",
        "title": "PR #115 & #150 land 132 reviewed Lean 4.36 cleanup files",
        "detail": "First two reviewed community batches merged cleanly onto v4.36.0 main (including #54, #62, #70, #71, #74-#76, #80-#82, #90, #92, #94), reducing backward.* directives and redundant proofs.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/150",
    },
    {
        "date": "2026-11-22",
        "tag": "Verification",
        "cls": "badge-verified",
        "title": "DeepMind formal-conjectures Comparator (#88) & 6+ independent checkers accept RH & GRH",
        "detail": "Full 61.57 GB export verified across con-leche, con-ron, con-agua, nanoda, Gruszka, and Pestka with zero sorry and standard axioms only.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/88",
    },
    {
        "date": "2026-11-22",
        "tag": "Toolchain Port",
        "cls": "badge-verified",
        "title": "PR #66 (@Vilin97) ports repository to Lean & Mathlib v4.36.0 + module system",
        "detail": "Migrated 164k files to Lean 4.36 module headers and pruned 15,068 unreachable dead files (-1.38M lines), establishing the live community cache baseline.",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/66",
    },
    {
        "date": "2026-11-21",
        "tag": "Dead Prune",
        "cls": "badge-dead",
        "title": "PR #45 (@rohanarun) removes 10,718 unreachable dead modules (-785K lines)",
        "detail": "First major structural slimming after v0.2.1, followed by active-cone explicit-dump cleanups (#57, #60, #65, #68).",
        "url": "https://github.com/leanprover-community/riemann-hypothesis/pull/45",
    },
    {
        "date": "2026-11-21",
        "tag": "Release",
        "cls": "badge-exact",
        "title": "v0.2.1 Verified RH/GRH Baseline Released (175,187 files · 17.37M lines)",
        "detail": "Public release of Levent Alpoge formal Lean 4 proof of the Riemann Hypothesis and Dirichlet GRH into leanprover-community/riemann-hypothesis.",
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

---
name: bohrium-rh-camp
description: >-
  Work a Riemann Hypothesis core pillar end to end around this tracker: read the
  public Bohrium Playground board, build the pillar's Lean proof locally, optionally
  run the heavy build on Bohrium compute with the `bohr` CLI, and submit a shorter
  proof through the Playground CLI. Every authenticated step is skipped silently when
  no credential is present. Use when a pillar needs a shorter verified proof, when a
  board number on the dashboard must be reproduced, or when a camp run must be moved
  to cloud compute.
compatibility: "Local Lean build needs elan/lake plus a Mathlib cache. The optional compute and submission steps need the Bohrium CLI (`bohr`, npm @dptech-corp/bohr-cli) and a Bohrium or Playground credential supplied by the owner. No credential is bundled here."
---

# Bohrium RH Camp

This skill connects three things: the Playground board that this repository tracks,
the Lean proof that satisfies one core pillar, and the Bohrium compute platform that
can carry the heavy `lake` build. It is derived from the two MIT-licensed upstream
projects [dptech-corp/bohrium-skills](https://github.com/dptech-corp/bohrium-skills)
(`bohrium-setup`, `bohrium-job`) and
[dptech-corp/bohr-agent-sdk](https://github.com/dptech-corp/bohr-agent-sdk); the
wording and the workflow here are written for this camp, not copied command tables.

## Rules that never change

- A token, access key, or password stays in the CLI's own credential store. Never
  write one into this repository, a JSON file, a commit, or a chat message.
- Missing credential means skip. Do not ask the owner for a secret in the middle of
  a build; do the public and local parts and report the authenticated step as
  pending.
- A submitted request is not a finished job and a scored submission is not a merged
  upstream commit. Report the terminal state you actually observed.
- Never invent a trace, a token count, or an axiom status. The board verifies; this
  repository only stores what the board returns.

## 1. Read the board (public, no credential)

The board is public JSON. Do not scrape the HTML page.

```bash
python scripts/fetch_verifytask.py --data data/verifytask_board.json
```

The normalized file carries one row per core pillar (`cores[]`), the `main`-tier
Grand Challenge (`grand`), the board's own model x harness ranking
(`benchmark.top_pairs`), repository coverage (`coverage`), the aggregate frontier,
and the curated timeline. If the fetch fails the previous file is kept, so a broken
network never blanks the dashboard.

Pick the target pillar from `cores[]` and record its `key`, `url`, `baseline_tokens`,
and `best_tokens`. That row is the number any new proof has to beat.

## 2. Build the proof locally

Build inside a scratch Lean project pinned to the challenge's Mathlib revision, never
inside this repository (this repository tracks no `.lean` tree and no `.lake` cache).

```bash
lake env lean Core<N>/Solution.lean
```

A cold Mathlib load dominates the wall clock. Keep the build in the scratch project
and copy only the final source where the submission expects it. Check the axioms the
challenge asks for (`#print axioms`); the board rejects anything outside the declared
closure.

## 3. Optional: run the build on Bohrium compute

Only if the owner has signed the CLI in. Check before spending:

```bash
bohr --version
bohr auth status
bohr doctor
bohr billing pricing --resource job -o json
bohr machine list --scene job --choose-type all -o json
```

If `bohr` is missing or `auth status` is not signed in, stop here and stay local. Do
not switch to the raw HTTP API to work around a missing CLI; the CLI carries the
credential and the billing confirmation.

Submit one Lean build as a job, after confirming project, machine, image, command,
input directory, result path, and the spending authorization with the owner:

```bash
bohr job submit --project-id <project_id> --job_name rh-core<N> \
  --image_address <image> --machine_type <machine> \
  --command "lake env lean Core<N>/Solution.lean > build.log 2>&1" \
  --input_directory ./input --result_path /personal/results --yes -o json
```

Read the Bohr ID from the successful response (`data.bohrJobId`), then poll the job
itself rather than the submission response:

```bash
bohr job describe --id <bohr_job_id> -o json
bohr job log <bohr_job_id>
bohr job download <bohr_job_id> --out ./results -o json
```

Treat the job as finished only when `phase` is terminal and `exitCode` is `0`; a
queued, running, or accepted response is not completion. Stop running jobs with
`bohr job terminate` and queued jobs with `bohr job kill`; both are resource actions,
so confirm the target first.

## 4. Submit to the Playground

**Gate first, every time.** Never submit a proof that cannot beat the current best.
Run the pre-submit gate and submit only when it exits `0`:

```bash
python -I scripts/playground_submit_gate.py --challenge-id <slug>   --tokens <our token count> --local-baseline <our count of the original closure>   --t0 <statement's 50-point baseline> [--predicted <other estimate>]...
```

The gate takes the lowest of the formula prediction and every `--predicted` value
and compares it with the best final `displayScore` across all attempt pages of the
public attempts API. Exit `0` = predicted score is strictly above the best, submit.
Exit `3` = HOLD: go back to step 2 with `improve.target_official_tokens_below` as the
token target. Exit `2` = the board could not be read: HOLD, never submit blind.
Every decision is appended to `data/playground_submissions.jsonl`; commit it.
The owner's submit command must be chained after the gate (`gate && playground submit`)
so a HOLD stops it.

The Playground challenge page (`https://play.bohrium.com/challenges/<slug>`) owns the
submission flow and its CLI. Follow that page's current instructions for the target
pillar. The submission credential comes from the owner's Playground dashboard; keep
it in the CLI's store, never in this repository. When the credential is absent, leave
the submission pending and report the exact command the owner has to run.

Record only what the board returns after submission (also as a ledger line with
`attempt_id`): attempt id, score, kept/not kept, and the board's verified status. Then refresh `data/verifytask_board.json`
with step 1 so the dashboard reflects the new attempt.

## What to report back

State the pillar key, the baseline to best token count you measured, the axiom
closure, whether the build ran locally or on Bohrium, the board attempt id and score
if the submission was accepted, and the exact step that is still waiting on a
credential.
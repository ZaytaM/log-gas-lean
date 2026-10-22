# Verification gate and its evidence

Status (2026-10-22): the paper theorem is **proved and machine-checked** in the sense below;
the certification record that says what that means and what still rests on humans is in
`Audit/` (start with `Audit/README.md`).

## Targets

* `PaperChallenge.lean` (imports only Mathlib) defines `LogGasPaper.PaperTheorem` and
  `LogGasPaper.LogKernelExists`. `PaperSolution.lean` repeats those definitions verbatim, imports the
  library `LogGas`, and provides `LogGasPaper.main : PaperTheorem` and
  `LogGasPaper.kernel_exists : LogKernelExists`.
* `Challenge.lean` / `Solution.lean` do the same for the earlier conditional H1/H2 target
  (`LogGasChallenge.principalStatement`, `bulkStatement`; `principal`, `bulk`).

## The gate: `scripts/verify.py --fresh`

Run from the project directory on a machine with the pinned toolchain. It creates an empty build
directory, rebuilds everything against the pinned dependency artifacts, and records commands,
exit codes, timings and hashes under `logs/verification/<timestamp>/` (`report.md`, `result.json`,
`freeze.json`, environment exports, command logs). Checks, in order:

1. `source-coverage`: every milestone declaration of `contracts.json` exists.
2. `source-provenance`, `source-locators`: the challenge files and the `notes/` excerpts are
   unchanged (hashes in `contracts.json`); every source locator resolves.
3. `challenge-direct-imports`: `Challenge.lean` and `PaperChallenge.lean` import only `Mathlib`.
4. `source-admissions`: no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `skipKernelTC` in
   the comment-stripped proof text.
5. `dependency-lock`, `installed-dependency-revisions`: `lake-manifest.json` equals
   `dependency-lock.json`; every installed dependency is at the pinned Git revision.
6. `fresh-directory`, `lean-version`, `project-build`, `fresh-lean-path`, `toolchain-prefix`,
   `no-old-project-artifacts`, `fresh-project-artifacts`: the build is really fresh and really
   the pinned toolchain.
7. `*-environment`, `independent-definition-parity`, `paper-definition-parity`: definitions in
   Challenge vs Solution (and PaperChallenge vs PaperSolution) are expression-identical (binder
   display names and metadata ignored); `*-mathlib-closure`: the challenges' import closure is
   inside Mathlib's.
8. `target-proof-contracts`, `paper-proof-contracts`: `example : principalStatement := principal`
   etc. elaborate, and `#print axioms` on the four targets is exactly `propext`, `Classical.choice`,
   `Quot.sound`.
9. `lean-kernel-replay`, `paper-kernel-replay`: `leanchecker` on `Solution` and `PaperSolution`
   (Lean's own kernel, fresh process).
10. `external-comparator`: an external checker supplied with `--comparator-argv`; otherwise
    recorded **UNPERFORMED**, never passed. The independent-kernel replay lives in `Audit/Replay/`
    and produces its own receipt; it is not run by this script.
11. `review-mathematical-fidelity`, `review-lean-verification`, `distinct-reviewers`: receipts under
    `verification/reviews/` from two distinct reviewers matching the current freeze.
12. `frozen-inputs-unchanged`: the freeze re-hashed after everything ran is identical.

`overall` is `passed` only if **every** check is `passed`; one `unperformed` check gives
`incomplete` (exit 1). `--structural-only` skips Lean entirely and can never pass.

## Last run

`logs/verification/20261022T042658Z/`: 31 passed, 1 unperformed (`external-comparator`) →
`overall: incomplete`. The four targets depend only on `propext`, `Classical.choice`, `Quot.sound`;
`leanchecker` accepted both solution modules; definition parity 14/14 with no differences.

## What the gate does not establish

* That `PaperTheorem` is the paper's Theorem 1.1: see `Audit/SIGNOFF.md`, `Audit/statement_map.md`,
  `Audit/reviews/`.
* That the hypothesis `LogHLS g B` is satisfiable: not proved here (`Audit/README.md`, layer 4).
* Independence from Lean's own kernel: `Audit/Replay/` (lean4export + Nanoda on fac5).

## Contracts and dependencies

`contracts.json` records the SHA-256 of each `notes/` excerpt, the milestone declarations with their
source labels, and a conservative prerequisite graph. The `module` field of each node is the module
that *declares* the milestone at the freeze (several milestones were built in modules other than
the one originally planned). `dependency-lock.json` is byte-for-byte dell3's installed manifest; for a
separate checkout restore it as `lake-manifest.json` and never run an unconstrained `lake update`.

## Reviews

`reviews/` holds the campaign-internal receipts (`mathematical-fidelity`, `lean-verification`,
2026-10-22, Sonnet workers of the same campaign) and will hold the fresh-context external reviews
of `Audit/reviews/REVIEW_INSTRUCTIONS.md`. Each receipt records role, reviewer identity, verdict and
the hashes of every reviewed file; a later source or harness change invalidates it.

# Certification record for the log-gas formalization

Project: Lean 4 formalization of Theorem 1.1 (uniform partition bound) of
*An entropy bound for the attractive logarithmic gas* (Delgadino, Gvalani, Rosenzweig).
Statement of record: `PaperChallenge.lean` (`LogGasPaper.PaperTheorem`, `LogGasPaper.LogKernelExists`);
proofs: `PaperSolution.lean` (`LogGasPaper.main`, `LogGasPaper.kernel_exists`) over the library `LogGas/`.
Toolchain `leanprover/lean4:v4.36.0-rc1`; Mathlib `625d8914199bc567cca9b91f90e8e5afafa5ae51` (`verification/dependency-lock.json`).

This directory is modelled on the certification record of the DGPS-LSI project. It separates
what is machine-checked from what rests on human sign-off, and records both.

## Layers

| Layer | Artifact | Status (2026-10-22) |
|---|---|---|
| 1. Manuscript of record | `MANUSCRIPT.md`, `manuscript/`, `tex_numbering.txt` | recorded |
| 2. Frozen statement layer | `FREEZE.md`, `frozen_statements.sha256`, `statement_types.{lean,txt}`, `check_statement_types.py`, `approved_changes.txt` | frozen at the commit named in `FREEZE.md`; **owner sign-off pending** (`SIGNOFF.md`) |
| 3. Statement map and fidelity reviews | `statement_map.md`, `reviews/` | map written; campaign-internal reviews recorded; **fresh-context external review pending** |
| 4. Non-vacuity | — | `LogKernelExists` proved; satisfiability of `LogHLS g B` for some `B > 0` (Beckner–Onofri input) **to be imported** from a separate Lean project |
| 5. Independent-kernel replay | `Replay/` | design and runner written; **run on fac5 pending** |

## What is machine-checked today

`scripts/verify.py --fresh` at the frozen commit (evidence `logs/verification/20261022T042658Z/`):
fresh build in an empty build directory against the pinned Mathlib; `PaperChallenge.lean` and
`Challenge.lean` unchanged and importing only `Mathlib`; no `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe`/`skipKernelTC` in the proof text; `example : LogGasPaper.PaperTheorem := LogGasPaper.main`
(and the other three targets) elaborate; `#print axioms` on all four targets shows only `propext`,
`Classical.choice`, `Quot.sound`; definition parity between Challenge and Solution environments
(14/14, no differences); `leanchecker` replay of `Solution` and `PaperSolution` (Lean's own kernel,
fresh process); two campaign-internal review receipts matching the freeze.

## Limits

* The machine checks show that the proofs establish the statements **as defined in
  `PaperChallenge.lean`**. That those definitions are the paper's theorem rests on the owner
  sign-off (`SIGNOFF.md`) and the fidelity reviews (`reviews/`), not on any tool.
* `leanchecker` uses Lean's own kernel; the independent-kernel replay (`Replay/`) has not run yet.
* `PaperTheorem` is conditional on the log-HLS hypothesis `LogHLS g B`, exactly as the paper's
  Theorem 1.1 is conditional on (1.3). No Lean proof yet shows that hypothesis is satisfiable
  (layer 4).
* The formalization follows the proof of the *short draft* (see `MANUSCRIPT.md`); the statement
  is compared against the *canonical* manuscript's Theorem (`SIGNOFF.md`, item S1).

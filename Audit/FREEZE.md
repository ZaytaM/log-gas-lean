# Statement-layer freeze

Date: 2026-10-22. Commit: edec32e (FREEZE_COMMIT).
commit that introduces this record).

## What is frozen

The *statement layer* is exactly the two files that define what is claimed, and nothing else:

* `PaperChallenge.lean` — namespace `LogGasPaper`: `Torus`, `uniform`, `radius`, `negCharacter`,
  `fourierCoeff`, `latticeNorm`, `cd`, `kernelCoeff`, `IsLogKernel`, `LogKernelExists`,
  `LogAsymptotic`, `FiniteEntropyDensity`, `relEntropy`, `logEnergy`, `LogHLS`,
  `LogHLSWithDomain`, `offDiagEnergy`, `partitionFunction`, `PaperTheorem`,
  `PaperTheoremPerKernel`, and the two trivial theorems `LogHLSWithDomain.toLogHLS`,
  `PaperTheorem.perKernel`.
* `Challenge.lean` — namespace `LogGasChallenge`: the conditional H1/H2 target
  (`principalStatement`, `bulkStatement` and the definitions they use).

Both import only `Mathlib`. Their SHA-256 are in `frozen_statements.sha256`
(`shasum -a 256 -c Audit/frozen_statements.sha256`). Git history: `PaperChallenge.lean` was
created in commit `e0c2f4d` (2026-10-21 17:03 CDT, *before* any proof of it was attempted) and
has not changed since; `Challenge.lean` was created in `7116f64` (2026-10-21 15:24 CDT) and has
not changed since. `verify.py`'s `frozen-inputs-unchanged` and `source-provenance` gates
re-check this on every run.

The *milestone statements* of the proof architecture (the 24 declarations listed in
`statement_map.md`, Block 2, e.g. `LogGas.Main.theorem11`, `LogGas.Bulk.lemma41`,
`LogGas.Singular.lemma51`) live in proof files and are **not** file-frozen: proof bodies there may
change. Their elaborated types are frozen instead, through the type baseline below.

## Pins

* Toolchain `leanprover/lean4:v4.36.0-rc1` (`lean-toolchain`).
* Mathlib `625d8914199bc567cca9b91f90e8e5afafa5ae51` and every dependency revision
  (`verification/dependency-lock.json`, byte-identical to `lake-manifest.json`; checked by
  `verify.py` gates `dependency-lock`, `installed-dependency-revisions`).

## Type baseline

`statement_types.lean` prints, with `pp.all`, the type of every declaration in namespaces
`LogGasPaper` and `LogGasChallenge` (and the value of every definition there), plus the types of the
24 milestone declarations and the `LogGas.Spec`/`LogGas.Torus` definitions they are stated with.
Its output at the freeze is `statement_types.txt`. Before any commit that touches a frozen file
or a milestone statement:

    lake env lean Audit/statement_types.lean > /tmp/st.txt
    python3 Audit/check_statement_types.py /tmp/st.txt

must report every baseline declaration identical (new helper declarations are allowed and
listed). `scripts/freeze.sh` regenerates both files and the hash list.

## Rules

* Changing any frozen statement or definition (hypotheses, conclusion, or a definition's body),
  or the type of a milestone declaration, needs the owner's written approval, recorded in
  `approved_changes.txt` as the expected new `pp.all` block, with a dated entry below.
* Proof bodies may change freely. Additive imports and new helper declarations are allowed.
* Any change to the two frozen files invalidates all review receipts under
  `verification/reviews/` and the replay receipts under `Audit/Replay/`; both must be redone.

## Sign-off

Pending: see `SIGNOFF.md`. Until the owner signs, this freeze records *what the campaign
proved*, not *what the authors claim*.

## Hash regeneration log

* 2026-10-22: initial freeze at `FREEZE_COMMIT`. Baseline generated on dell3 against the pinned
  toolchain. (The cosmetic docstring correction in `PaperSolution.lean` — "Only `Mathlib` is
  imported" was copied from the challenge and is false for the solution — is part of this
  commit; `PaperSolution.lean` is not a frozen file, but the change invalidates the 2026-10-22
  campaign-internal review receipts, which are superseded by the reviews of layer 3.)

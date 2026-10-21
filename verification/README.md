# Source coverage and final verification

The final mathematical proof is **incomplete**. The closed 107-task queue covered
existing proof placeholders; it did not cover declarations never written.
`LogGas/Bulk.lean` ends with the `KHyp` definition, and `LogGas/Main.lean` is absent.
In particular neither `LogGas.Bulk.lemma41` nor `LogGas.Main.theorem11` exists.

## Independent target

`Challenge.lean` imports only Mathlib and defines readable mathematical
propositions `LogGasChallenge.principalStatement` and `bulkStatement`. These are
specifications, not proved theorems. They contain no deliberate `sorry` holes.
The principal target is the conditional H1/H2 version on the period-one torus,
with normalized product Haar measure and the Euclidean product-circle radius.
The log-HLS hypothesis explicitly requires finite joint energy on finite-entropy
densities; totalized real integrals cannot silently supply that domain condition.
The partition is an extended nonnegative integral, so divergence cannot count
as zero. Its finite constant precedes all particle numbers and temperatures.

The specification takes the kernel as supplied data; correspondence with the
paper's particular Fourier-normalized logarithmic kernel remains a concrete
application/review obligation. No claim of full paper correspondence is made.
H1 and H2 are the authorized external inputs, and no output estimate is a model
field. A.e. kernel identities are appropriate for independent Haar particles;
bridges to pointwise abstract interfaces must justify their representatives.

`Solution.lean` independently repeats the explicit specification definitions and
imports the checked proof library, never Challenge. It currently supplies no
inhabitants. Future proofs must provide `LogGasChallenge.principal` and
`LogGasChallenge.bulk` of exactly the corresponding proposition types. The
verification gate fails until those actual bridge proofs exist. Copying a
statement or compiling a proposition is never counted as solving it.

## Dependencies and agent assignments

`contracts.json` records source hashes, expected source milestones and prerequisite
edges. It is a conservative milestone graph, not an exhaustive proof-term graph.
Missing auxiliary identifiers are provisional interfaces; the principal and bulk
names are explicitly required by the original phase notes. The initial
`proof_files` snapshot records historical support provenance, not an immutable
restriction preventing subsequent proofs. The final freeze binds actual files.

Named milestone workers run only when their prerequisites are axiom-clean on
main. Auxiliary workers receive source context but are not claimed to have a
complete automatically extracted prerequisite graph. Worker packets name source
passages, source hashes, scope and reusable prerequisite declarations. Physical
grid, singular-kernel and logarithmic exponential-integrability instances are
separate application nodes; abstract implications do not discharge them.
The service exits with `needs_implementation` when its proof queue closes but
required source declarations are absent. It does not manufacture placeholder
proofs or launch unlimited agents to hide missing implementation.

## Run on Dell3

From the project directory:

```
python3 scripts/verify.py --fresh
python3 -m unittest discover -s scripts/tests -v
```

`--fresh` creates a separate initially empty project build directory while using
the already pinned installed dependency artifacts. It records the actual Lean
path, commands, exit codes, timings and hashes. Existing deprecation/linter
warnings are retained; a warning-free development is not claimed. The complete
imported local declaration environment, including private/generated declarations,
is scanned for unsafe definitions, local axioms and forbidden transitive axioms.
Challenge's actual import closure must be a subset of Mathlib's independently
observed import closure. Solution must not import Challenge. Separate environments
export definition types/bodies for exact structural diagnostics. Actual proof
inhabitants are checked by Lean against the independent proposition definitions.
Expression parity ignores binder display names and metadata only. It is
supplementary, not a substitute for semantic review or
an external Comparator.

The preserved `dependency-lock.json` is byte-for-byte Dell3's installed manifest.
The gate checks the runtime manifest and every installed dependency Git revision.
For a separate checkout, restore it as `lake-manifest.json` before materializing
those exact dependencies. Do not run an unconstrained `lake update`.

An installed genuine Comparator runner may be supplied using `--comparator-argv`
with a JSON argument array. Its actual command and exit status are retained;
without it that check is **unperformed**, never passed. No external-kernel or
Comparator success is currently claimed. Lean's own `leanchecker` replay, when
available, is recorded separately. `--structural-only` always leaves Lean
verification unperformed and can never produce overall success.

Evidence goes to `logs/verification/<timestamp>/`: report.md, result.json,
freeze.json, separate environment exports and command logs. Exit 1 means
incomplete/failed verification. Missing source milestones, missing proofs,
missing/stale/unsuccessful independent reviews and unavailable required checks
all prevent an overall pass.

## Independent final reviews

The user requested two actual independent roles: mathematical fidelity and Lean
verification. Both inspect the same final source/configuration/harness freeze;
reviews with findings remain findings. Their reports and machine receipts are
under `verification/reviews/`. Each receipt records role, actual reviewer,
verdict and all reviewed file hashes (excluding review reports/receipts to avoid
self-reference). Distinct reviewer identities and matching hashes are required.
A reviewer does not patch the candidate or certify unperformed checks. A later
source or harness change invalidates the receipts and requires affected recheck.

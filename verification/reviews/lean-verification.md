# Independent Lean verification review

Reviewer: `/root/verification_review`
Verdict: **findings — final mathematical verification is incomplete**.

This review covers the exact 54-file candidate freeze in the accompanying JSON
receipt. I independently read the contracts, scheduler changes, tests, independent
specifications, environment audit and verification driver. I inspected the actual
Dell3 logs through read-only SSH and compared the complete remote freeze with the
local freeze: all 54 hashes match. I made no candidate changes and ran no Lean
builds or model workers as part of this review.

## Observed execution

Evidence directory on Dell3:
`/home/mgd885/work/loggas-verification-20261021/logs/verification/released-harness/`.
The run began at `2026-10-21T20:16:28Z`.

| Check | Actual result |
| --- | --- |
| Lean | 4.36.0-rc1, commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e` |
| Corrected regression suite | 23 tests passed, 62.027 seconds |
| Fresh project build | Passed, 18,133 jobs, 170.06 seconds |
| Fresh artifact isolation | Passed; 10 fresh project `.olean` files; old project artifact path excluded |
| Dependency provenance | Preserved manifest matched; all 9 installed dependency revisions matched their pins |
| Source provenance and locators | Passed |
| Challenge imports | Mathlib-only direct imports; actual closure added no unexpected modules |
| Challenge environment | 18 local declarations audited |
| Solution environment | 536 local declarations audited, including private/generated declarations |
| Independent specification parity | All 18 exported definitions matched after alpha-name/metadata normalization |
| Actual proof exports | Failed: `LogGasChallenge.principal` and `LogGasChallenge.bulk` are absent |
| Lean kernel replay | `leanchecker Solution` passed, 47.43 seconds |
| External Comparator | Unperformed; no genuine runner was configured |
| Frozen inputs | Unchanged throughout execution |

The kernel replay and declaration audit certify the development that currently
exists. Compiling the propositions in `Solution.lean` does not prove them.

## Harness assessment

The final gate fails closed on missing required source declarations, missing
proof inhabitants, forbidden axioms, changed input hashes, unsuccessful reviews
and unperformed mandatory checks. Structural-only mode cannot produce overall
success. The actual target check uses Lean type checking, rather than treating
statement text or a closed work queue as a theorem proof.

The environment scan selects declarations by their defining module, including
generated/private declarations, and checks their transitive axioms. It rejects
custom local axioms, unsafe declarations and axioms other than `propext`,
`Classical.choice` and `Quot.sound`. This is stronger coverage than a source
parser's named-theorem count.

The expression normalization removes binder display names and elaborator
metadata only; constants, universe levels, types, terms and de Bruijn indices
remain. Its parity result is useful diagnostic evidence, not an external
Comparator or an independent mathematical correspondence proof.

The fresh-artifact check resolves relative paths and symlinks and admits the
fresh project output, exact pinned package artifact roots and actual toolchain
core library. Dependency artifacts are shared and pinned, rather than rebuilt
from source by this run.

The milestone DAG is acyclic and binds source passages to named obligations.
Named consumers wait for axiom-clean prerequisites; the controller regression
tests exercise that scheduling behavior. Auxiliary workers receive source
packets but do not have a claimed exhaustive automatically extracted dependency
graph. Missing declarations produce `needs_implementation`, rather than a false
completion state or invented proof tasks.

## Blocking findings and required next work

The source-coverage check finds **16 absent declarations** across the 19
milestones. These include the bulk bound `LogGas.Bulk.lemma41`, final assembly
`LogGas.Main.theorem11`, and concrete torus/grid, singular-kernel and exponential
integrability bridges. The JSON receipt lists every missing declaration.

Implement those mathematical obligations and the two actual independent target
proof exports, while preserving the authorized H1/H2 assumptions. Configure and
run a genuine external Comparator if its verification claim is required. Then
repeat the final checks and both independent reviews on the resulting new
freeze. This receipt records a completed review with findings, never a pass for
the final paper theorem.

The released run finished before this receipt was supplied, so its stored
review checks report a missing verification receipt and an older remote
fidelity receipt. The accompanying local receipts bind the same verified final
freeze. Reporting their presence later must not relabel their `findings`
verdicts as successful reviews.

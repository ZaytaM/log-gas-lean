# Persistent Lean verification

Updated: 2026-10-21T04:18:46+00:00

State: running.
Workers configured: 6; active: 1.
Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.

- blocked: 4
- closed: 71
- pending: 29
- running: 1
- waiting_dependencies: 2

Attempts: 174; reported cost: $25.8057; attempts with unknown/incomplete usage: 1.
Queue is eligible to dispatch work.

Costs are client estimates and do not measure subscription allowance precisely.
Closed means the target proof passed source, build and axiom checks on main.
Waiting_dependencies means a proof is present but its transitive axiom audit is not yet clean; no model worker is spent on it.

## Needs attention

- LogGas.Decoupling.vanishing_word: Worker changed a statement or material outside its target proof
- LogGas.Singular.integral_QJ: Worker changed a statement or material outside its target proof
- LogGas.Singular.label_decomposition: Worker changed a statement or material outside its target proof
- LogGas.Singular.hker_trunc_tendsto: Worker changed a statement or material outside its target proof

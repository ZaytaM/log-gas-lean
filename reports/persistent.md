# Persistent Lean verification

Updated: 2026-10-21T06:19:14+00:00

State: running.
Workers configured: 6; active: 1.
Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.

- blocked: 4
- closed: 90
- pending: 12
- running: 1

Attempts: 234; reported cost: $31.3573; attempts with unknown/incomplete usage: 1.
Queue is eligible to dispatch work.

Costs are client estimates and do not measure subscription allowance precisely.
Closed means the target proof passed source, build and axiom checks on main.
Waiting_dependencies means a proof is present but its transitive axiom audit is not yet clean; no model worker is spent on it.

## Needs attention

- LogGas.Decoupling.vanishing_word: Worker changed a statement or material outside its target proof
- LogGas.Singular.integral_QJ: Worker changed a statement or material outside its target proof
- LogGas.Singular.label_decomposition: Worker changed a statement or material outside its target proof
- LogGas.Singular.hker_trunc_tendsto: Worker changed a statement or material outside its target proof

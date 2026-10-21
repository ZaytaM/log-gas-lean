# Persistent Lean verification

Updated: 2026-10-21T02:36:11+00:00

State: waiting_quota.
Workers configured: 6; active: 0.
Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.

- blocked: 3
- closed: 43
- pending: 59
- waiting_dependencies: 2

Attempts: 117; reported cost: $18.4135; attempts with unknown/incomplete usage: 0.
Automatic retry: 2026-10-21T02:41:38+00:00 (authentication)

Costs are client estimates and do not measure subscription allowance precisely.
Closed means the target proof passed source, build and axiom checks on main.
Waiting_dependencies means a proof is present but its transitive axiom audit is not yet clean; no model worker is spent on it.

## Needs attention

- LogGas.Decoupling.vanishing_word: Worker changed a statement or material outside its target proof
- LogGas.Singular.integral_QJ: Worker changed a statement or material outside its target proof
- LogGas.Singular.hker_trunc_tendsto: Worker changed a statement or material outside its target proof

# Persistent Lean verification

Updated: 2026-10-21T00:57:19+00:00

State: running.
Workers configured: 6; active: 0.
Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.

- blocked: 1
- closed: 28
- pending: 75
- waiting_dependencies: 3

Attempts: 65; reported cost: $10.6526; attempts with unknown/incomplete usage: 0.
Automatic retry: 2026-10-21T01:12:49+00:00 (authentication)

Costs are client estimates and do not measure subscription allowance precisely.
Closed means the target proof passed source, build and axiom checks on main.
Waiting_dependencies means a proof is present but its transitive axiom audit is not yet clean; no model worker is spent on it.

## Needs attention

- LogGas.Decoupling.vanishing_word: Worker changed a statement or material outside its target proof

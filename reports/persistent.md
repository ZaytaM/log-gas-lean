# Persistent Lean verification

Updated: 2026-10-21T02:03:46+00:00

State: running.
Workers configured: 6; active: 5.
Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.

- blocked: 1
- closed: 39
- pending: 59
- running: 5
- waiting_dependencies: 3

Attempts: 109; reported cost: $15.6837; attempts with unknown/incomplete usage: 5.
Queue is eligible to dispatch work.

Costs are client estimates and do not measure subscription allowance precisely.
Closed means the target proof passed source, build and axiom checks on main.
Waiting_dependencies means a proof is present but its transitive axiom audit is not yet clean; no model worker is spent on it.

## Needs attention

- LogGas.Decoupling.vanishing_word: Worker changed a statement or material outside its target proof

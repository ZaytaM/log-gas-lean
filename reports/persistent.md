# Persistent Lean verification

Updated: 2026-10-21T20:26:33+00:00

State: needs_implementation.
Workers configured: 6; active: 0.
Task and estimated-dollar caps: disabled; subscription limits trigger automatic waiting.

- closed: 107

Attempts: 295; reported cost: $36.4072; attempts with unknown/incomplete usage: 0.
Queue is eligible to dispatch work.

Costs are client estimates and do not measure subscription allowance precisely.
Closed means the target proof passed source, build and axiom checks on main.
Queue completion does not certify source coverage or mathematical fidelity; run scripts/verify.py.
Waiting_dependencies / waiting_saved_dependencies means a complete proof awaits prerequisite proofs and a clean axiom audit; no model worker is spent on it.

## Needs attention

- Missing required declaration: LogGas.Bulk.histogram_box
- Missing required declaration: LogGas.Bulk.empEnergy_split
- Missing required declaration: LogGas.Bulk.empEnergy_le
- Missing required declaration: LogGas.Bulk.dual_log_hls
- Missing required declaration: LogGas.Bulk.ell_hist
- Missing required declaration: LogGas.Bulk.coarse_exp_bound
- Missing required declaration: LogGas.Bulk.rJ_bound
- Missing required declaration: LogGas.Bulk.W_le_coarse
- Missing required declaration: LogGas.Bulk.lemma41
- Missing required declaration: LogGas.Main.holder_split
- Missing required declaration: LogGas.Main.bulk_hypothesis
- Missing required declaration: LogGas.Main.parameter_choice
- Missing required declaration: LogGas.Main.theorem11
- Missing required declaration: LogGas.Torus.grid
- Missing required declaration: LogGas.Physical.singular_instance
- Missing required declaration: LogGas.Physical.log_exp_integrable

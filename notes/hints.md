# Hints for workers

Workers read this file before every attempt. Add a heading per lemma name and a few
lines under it. The advisor appends `VERDICT=strategy` payloads here automatically.

## general
- Prefer `Fin n` index types and `Finset.sum`; avoid `tsum`.
- For integrals use `MeasureTheory.integral`; for probability measures the typeclass is `IsProbabilityMeasure`.
- Independence of finitely many variables: `ProbabilityTheory.iIndepFun`; identical law: `IdentDistrib`.

## Decoupling / Grouped / Singular: integrability migration (2026-10-20)
- `Hyp.h_bdd` has been removed. `Hyp.h_int i j p hp` gives joint absolute-power
  integrability; centering and moment bounds are almost everywhere in the frozen variable.
- Use `ext_integrable_pow`, `ext_integrable_pow_left/right`, `ext_sample_integrable_pow`,
  `integrable_S_pow`, `integrable_D_pow`, and `integrable_word` for Fubini/integral sums.
- `holder_group` is an a.e. bound under `Measure.pi ν`; `holder_group_at` takes explicit
  good-slice integrability and moment premises. Never specialize an a.e. bound at an
  arbitrary frozen point. Pull it back with `measurePreserving_eval` and combine finite
  families with `ae_all_iff`.
- `Grouped.exists_bound_S` now has an explicit extra boundedness premise. General
  decoupling/grouped proofs cannot supply it. Use moment or exponential integrability.
- `Singular.BoxKernel` uses joint power integrability and a.e. centering/moments.
  `hker_integrable_pow_left/right/prod` and `hker_moment_integral` derive these from
  `hker_moment`. `hker_boxKernel` works for any `K.Sub s'`, including `s_r` itself;
  `hyp_hker_labels` passes the untruncated singular kernel directly to `Decoupling.Hyp`.
- An upper bound on a Bochner integral does NOT prove integrability: Lean sets that
  integral to zero when integrability fails. Establish exponential integrability from the
  nonnegative series or use the retained truncation/Fatou argument before converting
  a Bochner bound to a lintegral bound.
- Keep all definitions/statements and other proofs unchanged. The migration was applied
  centrally; workers repair only their assigned remaining proof.

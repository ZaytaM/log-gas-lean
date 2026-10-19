# Hints for workers

Workers read this file before every attempt. Add a heading per lemma name and a few
lines under it. The advisor appends `VERDICT=strategy` payloads here automatically.

## general
- Prefer `Fin n` index types and `Finset.sum`; avoid `tsum`.
- For integrals use `MeasureTheory.integral`; for probability measures the typeclass is `IsProbabilityMeasure`.
- Independence of finitely many variables: `ProbabilityTheory.iIndepFun`; identical law: `IdentDistrib`.

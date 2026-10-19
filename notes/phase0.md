# Phase 0 — pipeline test on inequality (3.1)

Source: notes/sec3-badevent.tex, equation `eq:rough-partition-bound`.
Target file: LogGas/Warmup.lean. Two statements, abstract form, no torus.

## P0.A Jensen for an average of exponents

Setting: a probability space (Ω, μ); N ≥ 1; functions f : Fin N → Ω → ℝ with
each exp(f i) integrable.

Statement:  ∫ exp( (1/N) Σ_i f i ω ) dμ(ω) ≤ (1/N) Σ_i ∫ exp( f i ω ) dμ(ω).

Proof idea: convexity of exp pointwise (ConvexOn.map_sum_le with equal weights
1/N), then integral_mono and integral_finset_sum. Integrability of the left side
follows from the pointwise bound by the right-hand integrand.

## P0.B Product bound for independent variables

Setting: N ≥ 2; X : Fin N → Ω → E independent, identically distributed with law
ν on a measurable additive group E; K : E → ℝ measurable; constant A ≥ 1 with
∫ exp(K(x - y)) dν(y) ≤ A for ν-a.e. x (the paper has equality with A = A_b).

Statement:  for each i,  ∫ exp( Σ_{j ≠ i} K(X i ω - X j ω) ) dμ(ω) ≤ A^(N-1).

Proof idea: condition on X i (Fubini on the product law), the inner integral
factors over j ≠ i by independence into a product of N-1 identical factors each
≤ A. Use `ProbabilityTheory.iIndepFun`, `integral_prod` or
`iIndepFun.integral_prod`-style lemmas, `Finset.prod_const`, `Finset.card_erase_of_mem`.

## Acceptance

Both theorems compile with no `sorry`; `#print axioms` shows only propext,
Classical.choice, Quot.sound. Record the number of worker attempts for each.

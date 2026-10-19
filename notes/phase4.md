# Phase 4 — Lemma 4.1 via Appendix A

Source: notes/appendixA.tex, notes/sec4-bulk.tex. Target file: LogGas/Bulk.lean.
Depends on Decoupling.lean (D7).

Setting: K : E → E → ℝ continuous, symmetric, ∫ K(x,y) dμ(y) = 0, nonnegative quadratic form,
and the entropy–energy hypothesis (4.1) with constant B > 0 (this is H1 applied to K; take it
as a hypothesis of the lemma). Grid of M cells as in Phase 3; V_M = mean-zero cell-constant
functions, finite-dimensional.

Statements:
  A1 histogram/fluctuation split (A.1): ν_N(A_a) = 0 for every cell.
  A2 energy projection and completed square (A.2)–(A.4) on the finite-dimensional space V_M.
  A3 entropy variational formula (A.5): for h ∈ V_M, log ∫ e^{Th} dμ ≤ ⟨h, Th⟩/(2B).
     Sub-lemma: Gibbs/Donsker–Varadhan inequality ∫ f dρμ − H(ρμ|μ) ≤ log ∫ e^f dμ; prove
     from Jensen for finite-entropy densities, or on the finite cell algebra first.
  A4 (A.6): ⟨h, T z_N⟩ = (1/N) Σ_i Th(X_i).
  A5 Gaussian identity (A.7): E e^{(tN/2)⟨z_N,Tz_N⟩} ≤ (1−t/B)^{−q_M/2}, via a Gaussian vector on
     V_M with covariance Σ^{−1}; Mathlib's multivariate Gaussian or an explicit finite-dimensional
     integral (q_M ≤ M−1 coordinates).
  A6 remainder kernel (A.8)–(A.9): ‖r_J‖_∞ ≤ 4 ω_K(√d/J).
  A7 (A.10): W_N(K) ≤ N⟨z_N,Tz_N⟩ + W_N(r_J) + 5‖K‖_∞.
  A8 Lemma 4.1 (A.11): sup_N sup_{β ≤ β0} E e^{(β/2)W_N(K)} < ∞ for β0 < B, via Hölder, A5, and D7
     applied to r_J with κ = ‖r_J‖_∞.
If A5 resists, state it as a hypothesis and record that in notes/hypotheses.md.
Acceptance: Bulk.lean builds with no sorry; A8 is `LogGas.Bulk.lemma41`.

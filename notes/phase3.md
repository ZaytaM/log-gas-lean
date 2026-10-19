# Phase 3 — Lemma 5.1, singular part

Source: notes/sec5-singular.tex, notes/sec1-setting.tex (boxes, QJ), notes/hypotheses.md (H2).
Target file: LogGas/Singular.lean. Depends on Grouped.lean (G3).

Abstract setting (no Fourier analysis): E = T^d modeled as a measurable space with the
uniform probability measure μ; a grid of M = J^d boxes A_a, each of measure 1/M, with
uniform box measures ν_a; box averaging QJ; a nonnegative kernel s_r : E → ℝ with the
properties of H2 (support within distance r, s_r ≤ (log(r/dist))_+, mean c_r ≤ C r^d).
Adjacency of boxes is a fixed relation with ≤ 3^d − 1 neighbors per box; s_r(x−y) = 0
unless the boxes of x, y are equal or adjacent (take this as part of H2).

Statements:
  S1 kernel split (5.2)–(5.3): s̃_r = a_r + h_r with h_r = (I−QJ)_x(I−QJ)_y s_r; both centered
     under μ in each variable; h_r centered under ν_a in each variable on every box product.
  S2 Cauchy–Schwarz (5.4).
  S3 averaging term bounds (5.5)–(5.6): ‖a_r‖_∞ ≤ C, sup_x ∫|a_r| ≤ 4c_r, and the moment bound
     with κ(r) = C'/log(1/r).
  S4 (5.7): E e^{tW_N(a_r)} ≤ 8/3 for J ≥ J0, via D7 with κ = κ(r), θ = 2t.
  S5 moment bound (5.8) for h_r under box measures with universal κ*.
  S6 occupancy decomposition (2.3)/(5.9): E[1_A F] = Σ_n π_N(n) E_n[F] over good occupancy vectors.
  S7 (5.10)–(5.11): E_n e^{tW_N(h_r)} ≤ (8/3)^M for each good n, via G3 with m* ≤ δN, K = 3^d.
  S8 Lemma 5.1: sup_N sup_{t ≤ t0} E[1_A e^{(t/2)W_N(s̃_r)}] ≤ (8/3)^{(M+1)/2}.
Acceptance: Singular.lean builds with no sorry; S8 is `LogGas.Singular.lemma51`.

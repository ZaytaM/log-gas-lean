# Phase 2 — grouped bound (6.4) and Section 3

Sources: notes/sec6-lemma61.tex (grouped conclusion), notes/sec3-badevent.tex.
Target files: LogGas/Grouped.lean, LogGas/BadEvent.lean.

Grouped.lean (depends on LogGas.Decoupling.exp_bound):
  G1 greedy edge coloring: a finite simple graph with max degree ≤ K-1 has a proper edge
     coloring with ≤ 2K-1 colors (SimpleGraph; prove by greedy induction on edges).
  G2 class independence: terms of S whose groups lie in different pairs of one color class
     are independent random variables.
  G3 (6.4): with M groups each of size ≤ m*, each interacting with ≤ K-1 others,
     E e^{uS/m} ≤ (8/3)^M whenever 4 K C_u κ |u| m*/m ≤ 1/2.  Proof: split S by color class,
     apply D7 to each block with θ = 2K u m_b/m, Hölder over the 2K classes.

BadEvent.lean:
  B1 Jensen average (= Phase 0 P0.A) — import from Warmup, do not restate.
  B2 rough bound (3.1): Z_{N,b} ≤ A_b^{N-1} (= Phase 0 P0.B specialized).
  B3 Hölder monotonicity: Z_{N,γ} ≤ Z_{N,b}^{γ/b} ≤ A_b^{N-1} for 0 ≤ γ ≤ b, using A_b ≥ 1.
  B4 binomial Chernoff with relative-entropy exponent: for X ~ Bin(N, q) and δ > q,
     P(X ≥ δN) ≤ exp(-N D(δ‖q)), D(δ‖q) = δ log(δ/q) + (1-δ) log((1-δ)/(1-q)).
     Prove from the moment generating function (Mathlib has Bin mgf) if not present.
  B5 (3.2): P(B_{N,J,δ}) ≤ M exp(-N D(δ‖1/M)) by union bound over M boxes.
  B6 (3.3): E[1_B e^{(β/2)W_N(g)}] ≤ M^{1/s'} exp{N(log A_b/s − D/s')} by Hölder with exponents s, s'.
Model the boxes abstractly: a measurable partition of E into M sets of ν-measure 1/M each;
occupancy n_a := #{i : X i ∈ A_a}. Acceptance: both files build with no sorry.

# Phase 5 — Theorem 1.1 assembly

Source: notes/sec1-setting.tex, notes/sec2-cutoff.tex (only eq. 2.3–2.4), notes/sec5-singular.tex
(Conclusion paragraph), notes/hypotheses.md. Target file: LogGas/Main.lean.
Depends on BadEvent (B6), Bulk (A8), Singular (S8).

Statements:
  M1 Hölder split (2.4): for conjugate p, q and the decomposition g = b_r + s̃_r from H2,
     Z_{N,β} ≤ (E e^{(pβ/2)W_N(b_r)})^{1/p} (E 1_A e^{(qβ/2)W_N(s̃_r)})^{1/q} + E 1_B e^{(β/2)W_N(g)}.
  M2 bulk hypothesis check: b_r satisfies the hypotheses of A8 with the same B (from H1 and H2).
  M3 parameter choice: given β0 < B, choose p, q, then δ ≤ δ0 and J ≥ J0 with J^{-d} < δ and
     the exponent in B6 negative; all independent of N.
  M4 Theorem 1.1: ∃ C, ∀ N ≥ 2, ∀ β ∈ [0, β0], Z_{N,β} ≤ C.
Final check: `#print axioms LogGas.Main.theorem11` shows only propext, Classical.choice,
Quot.sound; H1 and H2 appear as hypotheses of the theorem, not as axioms.

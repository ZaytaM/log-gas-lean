# Phase 1 — Lemma 6.1, one-block bound (6.3)

Source: notes/sec6-lemma61.tex. Target file: LogGas/Decoupling.lean.
Setting throughout: m ≥ 1; (Ω, μ) a probability space; Y : Fin m → Ω → E independent
(ProbabilityTheory.iIndepFun), each with law ν i on a measurable space E; kernels
h : Fin m → Fin m → E → E → ℝ, measurable, bounded, used only for i < j (h j i x y := h i j y x).
Hypotheses as in the paper, with essential suprema replaced by pointwise bounds:
  (6.1) centering: ∀ i<j, ∀ y, ∫ h i j x y d(ν i)(x) = 0 and ∀ x, ∫ h i j x y d(ν j)(y) = 0
  (6.2) moments: ∀ i<j, ∀ p ≥ 1, ∀ y, ∫ |h i j x y|^p d(ν i)(x) ≤ 2 κ^p p!  (and symmetrically in x).
S ω := Σ_{i<j} h i j (Y i ω) (Y j ω).

Statements, in dependency order (each its own lemma):
  D1 decoupling identity (6.5): for a Bernoulli(1/2) index set I independent of Y,
     E_I[D_I] = S/2 where D_I = Σ_{i∈I, j∉I} h i j (Y i) (Y j).
  D2 Jensen step (6.6): E|S|^{2k} ≤ 2^{2k} E_I E|D_I|^{2k}.
  D3 vanishing terms: a monomial in the expansion of D_I^{2k} in which some label occurs
     exactly once in the row word or the column word has expectation 0 (uses 6.1 + independence).
  D4 Hölder bound (6.9)–(6.10): |E ∏_{v} h_{i_v j_v}| ≤ 2^k κ^{2k} ∏_ℓ a_ℓ! for surviving words.
  D5 counting (6.12): A·B_k ≤ (4e²)^k m^{2k} when m ≥ 2k, and ≤ 2^{4k} m^{2k} when m < 2k;
     may be weakened to A·B_k ≤ C^k m^{2k} for a universal C.
  D6 moment bound: E|S|^{2k} ≤ (C_u κ m)^{2k} (2k)!.
  D7 exponential bound (6.13): E e^{θS/m} ≤ 2/(1-(C_u κ |θ|)²) when C_u κ |θ| < 1.
The universal constant C_u is existential: state D6/D7 as ∃ C_u, ∀ m κ h Y ..., or fix C_u := 8e.
Acceptance: Decoupling.lean builds with no sorry; D7 is `LogGas.Decoupling.exp_bound`.

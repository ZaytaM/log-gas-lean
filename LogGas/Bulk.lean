import LogGas.Singular

/-!
# Phase 4 — Lemma 4.1 (`lem:continuous-entropy-partition`) via Appendix A

Source: `notes/appendixA.tex`, `notes/sec4-bulk.tex`.  Phase notes: `notes/phase4.md`.
Depends on `LogGas.Decoupling.exp_bound` (D7) and on the boxes / box averaging of
`LogGas.BadEvent`, `LogGas.Singular`.

Setting.  `E` is the torus `T^d`, modelled abstractly exactly as in `LogGas.Singular` (the
group, metric and invariance instances are inherited only so that the box-averaging lemmas of
that file can be reused; Appendix A itself uses none of them).  `μE` is the uniform probability
measure.  The kernel `K : E → E → ℝ` is bounded measurable, symmetric, centered
(`∫ K(x,y) dμ(y) = 0`), with nonnegative quadratic form on bounded measurable functions, and
satisfies the entropy–energy inequality (4.1) with constant `B > 0`; these are collected in the
`Prop`-structure `KHyp`.  Uniform continuity enters only through the remainder bound (A.9) and
in Lemma 4.1 itself.  A grid `bx : Boxes μE M` of `M` cells of measure `1/M` is fixed; the
mean-zero cell-constant space `V_M` of the paper is represented by coefficient vectors
`c : Fin M → ℝ` through `cellFun bx c`.

Statements (phase notes A1–A8):
* A1 `histogram_box` — eq. `eq:empirical-histogram-splitting` (A.1), `ν_N(A_a) = 0`;
* A2 `square_completion`, `empEnergy_split`, `empEnergy_le` — eqs. (A.2)–(A.4);
* A3 `gibbs_identity`, `dual_log_hls` — eq. `eq:dual-log-hls` (A.5);
* A4 `empPair_cellFun` — eq. `eq:coarse-gaussian-pairing` (A.6);
* A5 `gaussian_mgf_linear`, `gaussian_quadratic_integral`, `coarse_particle_factor`,
  `coarse_exp_bound` — eq. `eq:coarse-partition-estimate` (A.7);
* A6 `rJ`, `rJ_bound` — eqs. `eq:general-cell-centering` (A.8),
  `eq:continuous-small-remainder` (A.9);
* A7 `W_le` — eq. `eq:diagonal-correction-bound` (A.10);
* A8 `lemma41` — eq. `eq:continuous-proof-conclusion` (A.11) / Lemma 4.1.

One deviation from the paper.  The energy projection `P_M(ν_N)` of (A.2) and the null
directions of the cell energy form are avoided by a regularization: for `ε > 0` the cell Gram
matrix `Σ` is replaced by `Σ_ε = Σ + ε·1`, which is positive definite, and the completed square
(A.4) is replaced by the elementary inequality
`2⟨h, Tμ_N⟩ − ⟨h, Th⟩ ≤ ℓ·Σ_ε⁻¹ℓ + ε|c|²` for the histogram `h = f_L` (coefficients `c`,
`|c|² ≤ M²`).  The Gaussian estimate (A.7) holds for `Σ_ε` with the exponent `M/2` in place of
`q_M/2` (`q_M ≤ M − 1`), uniformly in `ε`; choosing `ε = 1/N` in (A.10) costs the additive
constant `M²` in the exponent, which is harmless for (A.11).  Equally, the Donsker–Varadhan
supremum in (A.5) is only needed at the Gibbs density `e^{Th}/∫e^{Th}`, where it is an identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

/-! ### Abstract ingredients: Gibbs identity, finite-dimensional square completion, Gaussians -/

section Abstract

-- SKETCH: `Z := ∫ exp f > 0` (`integral_exp_pos`, or `integral_pos_iff_support_of_nonneg`
-- with `Real.exp_pos`).  Pointwise `log (exp (f x) / Z) = f x - log Z`
-- (`Real.log_div`, `Real.log_exp`, `Real.exp_ne_zero`), so the integrand is
-- `(exp f / Z) * f - (exp f / Z) * log Z`; `integral_sub`, `integral_mul_const` and
-- `∫ exp f / Z = 1` (`integral_div`, `div_self`).  Integrability of all terms from
-- `Integrable.of_bound` (bounded measurable, finite measure).
/-- Gibbs identity behind the entropy variational formula of eq. `eq:dual-log-hls` (A.5):
for the Gibbs density `ρ = e^f / ∫e^f` of a bounded measurable `f`,
`∫ ρ log ρ = ∫ f ρ − log ∫ e^f`. -/
theorem gibbs_identity {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    ∫ x, (Real.exp (f x) / ∫ y, Real.exp (f y) ∂ν)
        * Real.log (Real.exp (f x) / ∫ y, Real.exp (f y) ∂ν) ∂ν
      = (∫ x, f x * (Real.exp (f x) / ∫ y, Real.exp (f y) ∂ν) ∂ν)
          - Real.log (∫ y, Real.exp (f y) ∂ν) := by
  sorry

-- SKETCH: `Matrix.PosDef.add_posSemidef` is stated the other way round; use
-- `(Matrix.PosDef.smul Matrix.PosDef.one hε).add_posSemidef`-style reasoning after
-- `add_comm`, or `Matrix.PosDef.of_dotProduct_mulVec_pos` directly:
-- `c ⬝ᵥ (A + ε•1) *ᵥ c = c ⬝ᵥ A *ᵥ c + ε * (c ⬝ᵥ c)` (`Matrix.add_mulVec`, `Matrix.smul_mulVec`,
-- `Matrix.one_mulVec`, `dotProduct_add`, `dotProduct_smul`), the first term `≥ 0` by
-- `hA.dotProduct_mulVec_nonneg`, the second `> 0` for `c ≠ 0` (`dotProduct_self_pos`?,
-- `Matrix.dotProduct_self_eq_zero`).  Hermitian: `hA.1.add` with `isHermitian_one.smul`.
/-- The regularized Gram matrix `Σ_ε = Σ + ε·1` is positive definite. -/
theorem posDef_add_smul_one {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosSemidef)
    (ε : ℝ) (hε : 0 < ε) : (A + ε • (1 : Matrix (Fin q) (Fin q) ℝ)).PosDef := by
  sorry

-- SKETCH (A.2)–(A.3), regularized: put `Aε := A + ε•1`, `p := Aε⁻¹ *ᵥ ℓ`, so `Aε *ᵥ p = ℓ`
-- (`Matrix.mulVec_mulVec`, `Matrix.mul_nonsing_inv` with `(posDef_add_smul_one ..).isUnit`
-- / `Matrix.PosDef.det_pos`, `Matrix.one_mulVec`).  Then expand
-- `0 ≤ (c - p) ⬝ᵥ Aε *ᵥ (c - p)` (`Matrix.PosDef.posSemidef`, `dotProduct_mulVec_nonneg`)
-- with `Matrix.mulVec_sub`, `sub_dotProduct`, `dotProduct_sub`, symmetry
-- `Matrix.dotProduct_mulVec`, `Matrix.vecMul_transpose`, `hA.1.eq` to get
-- `2 (c ⬝ᵥ ℓ) - c ⬝ᵥ Aε *ᵥ c ≤ ℓ ⬝ᵥ Aε⁻¹ *ᵥ ℓ`, and finally
-- `c ⬝ᵥ Aε *ᵥ c = c ⬝ᵥ A *ᵥ c + ε (c ⬝ᵥ c)`.
/-- Eqs. `eq:explicit-histogram-square-shift`–`eq:histogram-square-shift` (A.2)–(A.3) in
regularized form: for a positive semidefinite `Σ`, every `ℓ`, `c` and `ε > 0`,
`2⟨c, ℓ⟩ − ⟨c, Σc⟩ ≤ ⟨ℓ, Σ_ε⁻¹ ℓ⟩ + ε |c|²` with `Σ_ε = Σ + ε·1`; the right-hand side is
the completed square at the regularized projection `Σ_ε⁻¹ ℓ`. -/
theorem square_completion {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosSemidef)
    (ε : ℝ) (hε : 0 < ε) (ℓ c : Fin q → ℝ) :
    2 * (c ⬝ᵥ ℓ) - c ⬝ᵥ A *ᵥ c
      ≤ ℓ ⬝ᵥ (A + ε • (1 : Matrix (Fin q) (Fin q) ℝ))⁻¹ *ᵥ ℓ + ε * (c ⬝ᵥ c) := by
  sorry

-- SKETCH: `L := CFC.sqrt A⁻¹` (`open scoped MatrixOrder`; `Matrix.PosDef.inv`,
-- `Matrix.nonneg_iff_posSemidef`, `CFC.sqrt_mul_sqrt_self`, `Matrix.PosDef.inv_sqrt`).
-- `L` is Hermitian (`Matrix.PosSemidef.isHermitian (CFC.sqrt_nonneg _)`), real, so `Lᵀ = L`
-- (`Matrix.IsHermitian.eq`, `conjTranspose_eq_transpose_of_trivial`) and `L * Lᵀ = L * L = A⁻¹`;
-- then `Lᵀ * A * L = L * (L * L)⁻¹ * L = 1` by `Matrix.mul_inv_rev`,
-- `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv` (`L` invertible: `Matrix.isUnit_iff_isUnit_det`,
-- `(hA.inv).det_pos` and `det_mul`).
/-- A positive definite matrix `A` admits a square root `L` of its inverse:
`L Lᵀ = A⁻¹` and `Lᵀ A L = 1` (the coordinates in which the Gaussian vector of
eq. `eq:coarse-partition-estimate` (A.7) is standard). -/
theorem exists_sqrt_inv {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosDef) :
    ∃ L : Matrix (Fin q) (Fin q) ℝ, L * Lᵀ = A⁻¹ ∧ Lᵀ * A * L = 1 := by
  open scoped MatrixOrder in
  focus
    classical
    have hI : A⁻¹.PosSemidef := hA.inv.posSemidef
    have hnn : (0 : Matrix (Fin q) (Fin q) ℝ) ≤ A⁻¹ := by
      exact Matrix.nonneg_iff_posSemidef.mpr hI
    have hLL : CFC.sqrt A⁻¹ * CFC.sqrt A⁻¹ = A⁻¹ := CFC.sqrt_mul_sqrt_self _ hnn
    have hLh : (CFC.sqrt A⁻¹).IsHermitian := by
      exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
    have hLT : (CFC.sqrt A⁻¹)ᵀ = CFC.sqrt A⁻¹ := by
      have := hLh.eq
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    generalize CFC.sqrt A⁻¹ = L at hLL hLh hLT
    have hdet : IsUnit L.det := by
      have h1 : IsUnit (L * L).det := by
        rw [hLL, isUnit_iff_ne_zero]; exact (hA.inv.det_pos).ne'
      rw [Matrix.det_mul] at h1
      exact (IsUnit.mul_iff.mp h1).1
    have hU : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr hdet
    have hAd : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hAd
    refine ⟨L, by rw [hLT, hLL], ?_⟩
    rw [hLT]
    rw [← hLL] at hAA
    apply (Matrix.isUnit_iff_isUnit_det L |>.mpr hdet |> fun h => (IsUnit.mul_left_inj h).mp)
    calc L * A * L * L = L * (A * (L * L)) := by simp only [mul_assoc]
      _ = 1 * L := by rw [hAA, mul_one, one_mul]

/-- The standard Gaussian measure on `ℝ^q = Fin q → ℝ`, as a product of `gaussianReal 0 1`. -/
noncomputable def stdGauss (q : ℕ) : Measure (Fin q → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (q : ℕ) : IsProbabilityMeasure (stdGauss q) := by
  unfold stdGauss; infer_instance

-- SKETCH: `v ⬝ᵥ (L *ᵥ g) = (Lᵀ *ᵥ v) ⬝ᵥ g = ∑ k, (Lᵀ *ᵥ v) k * g k`
-- (`Matrix.dotProduct_mulVec`, `Matrix.vecMul_transpose`, `dotProduct` unfolded); `Real.exp_sum`
-- turns the integrand into `∏ k, exp (w k * g k)`; `integral_fintype_prod_eq_prod` factors the
-- `Measure.pi`-integral; each factor is `mgf id (gaussianReal 0 1) (w k) = exp (w k ^ 2 / 2)`
-- (`mgf_gaussianReal` with `HasLaw id`, `mgf`); recombine with `← Real.exp_sum`,
-- `Finset.sum_div`, `sq`.
/-- "The elementary identity `𝔼_Z[e^{vᵀΣZ}] = e^{vᵀΣv/2}`" of
eq. `eq:coarse-partition-estimate` (A.7), for the linear image `Z = L g` of a standard Gaussian
vector `g`: `∫ exp(v·(L g)) dγ(g) = exp(|Lᵀ v|²/2)`. -/
theorem gaussian_mgf_linear (q : ℕ) (L : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    ∫ g, Real.exp (v ⬝ᵥ (L *ᵥ g)) ∂(stdGauss q)
      = Real.exp ((Lᵀ *ᵥ v) ⬝ᵥ (Lᵀ *ᵥ v) / 2) := by
  set w := Lᵀ *ᵥ v with hw
  have h1 : ∀ g : Fin q → ℝ, v ⬝ᵥ (L *ᵥ g) = ∑ k, w k * g k := by
    intro g
    rw [hw, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    rfl
  have h2 : ∀ g : Fin q → ℝ, Real.exp (v ⬝ᵥ (L *ᵥ g)) = ∏ k, Real.exp (w k * g k) := by
    intro g; rw [h1, Real.exp_sum]
  simp_rw [h2]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun k (x : ℝ) => Real.exp (w k * x))]
  have h3 : ∀ k, ∫ x, Real.exp (w k * x) ∂(gaussianReal 0 1) = Real.exp (w k ^ 2 / 2) := by
    intro k
    have := mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1)
      ⟨aemeasurable_id, by simp⟩ (w k)
    simp only [mgf, id] at this
    rw [this]; simp
  simp_rw [h3]
  rw [← Real.exp_sum, dotProduct]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

-- SKETCH: `exp ((s/2) * (g ⬝ᵥ g)) = ∏ k, exp ((s/2) * g k ^ 2)` (`dotProduct`, `Finset.mul_sum`,
-- `Real.exp_sum`); `integral_fintype_prod_eq_prod`, then the one-dimensional integral
-- `∫ exp ((s/2) x²) ∂gaussianReal 0 1 = (1 - s)^(-1/2)`: unfold the density
-- (`integral_gaussianReal_eq_integral_smul`, `gaussianPDFReal_def`), combine the exponents
-- (`← Real.exp_add`, `neg_mul`), and use `integral_gaussian (b := (1 - s)/2)`:
-- `√(π / ((1-s)/2)) / √(2π) = (1 - s)^(-1/2)` (`Real.sqrt_div`, `Real.sqrt_eq_rpow`,
-- `Real.rpow_neg`).  Finally `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin`,
-- `← Real.rpow_natCast`, `← Real.rpow_mul`.
/-- The Gaussian integral in eq. `eq:coarse-partition-estimate` (A.7):
`∫ exp((s/2)|g|²) dγ(g) = (1 − s)^{−q/2}` for `0 ≤ s < 1`. -/
theorem gaussian_quadratic_integral (q : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∫ g, Real.exp ((s / 2) * (g ⬝ᵥ g)) ∂(stdGauss q) = (1 - s) ^ (-(q : ℝ) / 2) := by
  sorry

-- SKETCH: `Real.exp_sum` gives the integrand `∏ i, exp (φ (X i ω))`; by
-- `iIndepFun_iff_map_fun_eq_pi_map` (with `hX_meas`, `hX_law`) the law of `ω ↦ (X · ω)` is
-- `Measure.pi (fun _ => ν)`, so `integral_map` (measurability: `measurable_pi_lambda`,
-- `Real.measurable_exp.comp (hφ.comp (measurable_pi_apply i))`) rewrites the left side as
-- `∫ x, ∏ i, exp (φ (x i)) ∂Measure.pi _`, which is `∏ i, ∫ exp (φ x) ∂ν` by
-- `integral_fintype_prod_eq_prod`; conclude with `Finset.prod_const`, `Finset.card_univ`,
-- `Fintype.card_fin`.  (Same computation as `LogGas.Warmup.prod_bound_indep` with `K`
-- replaced by a one-variable function.)
/-- "Tonelli and independence": for i.i.d. `X_i ∼ ν` and a bounded measurable `φ`,
`𝔼 e^{∑_i φ(X_i)} = (∫ e^φ dν)^N`, the particle integral in
eq. `eq:coarse-partition-estimate` (A.7). -/
theorem iid_exp_sum {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure α) [IsProbabilityMeasure ν]
    {N : ℕ} (X : Fin N → Ω → α) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = ν) (φ : α → ℝ) (hφ : Measurable φ) (C : ℝ)
    (hφC : ∀ x, |φ x| ≤ C) :
    ∫ ω, Real.exp (∑ i, φ (X i ω)) ∂μ = (∫ x, Real.exp (φ x) ∂ν) ^ N := by
  sorry

end Abstract

/-! ### Definitions: energy form, cell functions, histogram, coarse energy, remainder kernel -/

section Defs

variable {E : Type*} [MeasurableSpace E]

/-- The energy form `⟨f, T_K g⟩ = ∬ K(x,y) f(x) g(y) dμ(x) dμ(y)` on functions
(Appendix A, "for this proof write `T = T_K`"). -/
noncomputable def energy (μE : Measure E) (K : E → E → ℝ) (f g : E → ℝ) : ℝ :=
  ∫ x, ∫ y, K x y * f x * g y ∂μE ∂μE

/-- The integral operator `(T_K h)(x) = ∫ K(x,y) h(y) dμ(y)`. -/
noncomputable def T (μE : Measure E) (K : E → E → ℝ) (h : E → ℝ) (x : E) : ℝ :=
  ∫ y, K x y * h y ∂μE

/-- The cell-constant function `∑_a c_a 1_{A_a}` with coefficient vector `c`; the space `V_M`
of the paper is the set of these with `∑_a c_a = 0`. -/
noncomputable def cellFun {μE : Measure E} {M : ℕ} (bx : Boxes μE M) (c : Fin M → ℝ) (x : E) :
    ℝ :=
  ∑ a, (bx.A a).indicator (fun _ => c a) x

/-- The cell Gram matrix `Σ_{ab} = ⟨1_{A_a}, T_K 1_{A_b}⟩`, "the matrix of the energy form"
on cell-constant functions. -/
noncomputable def gram (μE : Measure E) (K : E → E → ℝ) {M : ℕ} (bx : Boxes μE M) :
    Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun a b => energy μE K ((bx.A a).indicator 1) ((bx.A b).indicator 1)

/-- The regularized Gram matrix `Σ_ε = Σ + ε·1`. -/
noncomputable def gramReg (μE : Measure E) (K : E → E → ℝ) {M : ℕ} (bx : Boxes μE M) (ε : ℝ) :
    Matrix (Fin M) (Fin M) ℝ :=
  gram μE K bx + ε • (1 : Matrix (Fin M) (Fin M) ℝ)

/-- The remainder kernel `r_J = (I − Q_J)_x (I − Q_J)_y K` of eq. `eq:general-cell-centering`
(A.8). -/
noncomputable def rJ {μE : Measure E} {M : ℕ} (bx : Boxes μE M) (K : E → E → ℝ) (x y : E) : ℝ :=
  K x y - QJx bx K x y - QJy bx K x y + QJx bx (QJy bx K) x y

variable {Ω : Type*} {N : ℕ}

/-- The histogram coefficients `M n_a / N` of `f_L` in eq. `eq:empirical-histogram-splitting`
(A.1). -/
noncomputable def histCoef {μE : Measure E} {M : ℕ} (X : Fin N → Ω → E) (bx : Boxes μE M)
    (ω : Ω) (a : Fin M) : ℝ :=
  M * (occupancy X (bx.A a) ω : ℝ) / N

/-- The histogram `f_L = (M/N) ∑_a n_a 1_{A_a}` of eq. `eq:empirical-histogram-splitting`
(A.1). -/
noncomputable def hist {μE : Measure E} {M : ℕ} (X : Fin N → Ω → E) (bx : Boxes μE M) (ω : Ω) :
    E → ℝ :=
  cellFun bx (histCoef X bx ω)

/-- The empirical energy `⟨μ_N, T_K μ_N⟩ = N⁻² ∑_{i,j} K(X_i, X_j)`. -/
noncomputable def empEnergy (K : E → E → ℝ) (X : Fin N → Ω → E) (ω : Ω) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, K (X i ω) (X j ω)

/-- The empirical pairing `⟨h, T_K μ_N⟩ = ∫ T_K h dμ_N = N⁻¹ ∑_i (T_K h)(X_i)`. -/
noncomputable def empPair (μE : Measure E) (K : E → E → ℝ) (h : E → ℝ) (X : Fin N → Ω → E)
    (ω : Ω) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, T μE K h (X i ω)

/-- The coefficient vector `ℓ_a = ⟨1_{A_a}, T_K μ_N⟩` of the linear functional
`h ↦ ⟨h, T_K μ_N⟩` on cell-constant functions. -/
noncomputable def ell (μE : Measure E) (K : E → E → ℝ) {M : ℕ} (bx : Boxes μE M)
    (X : Fin N → Ω → E) (ω : Ω) : Fin M → ℝ :=
  fun a => empPair μE K ((bx.A a).indicator 1) X ω

/-- The regularized coarse energy `⟨z_N, T z_N⟩_ε = ℓ · Σ_ε⁻¹ ℓ`, the completed square of the
histogram part (the role of `⟨z_N, T z_N⟩` in eqs. (A.4), (A.7), (A.10)). -/
noncomputable def coarse (μE : Measure E) (K : E → E → ℝ) {M : ℕ} (bx : Boxes μE M) (ε : ℝ)
    (X : Fin N → Ω → E) (ω : Ω) : ℝ :=
  ell μE K bx X ω ⬝ᵥ (gramReg μE K bx ε)⁻¹ *ᵥ ell μE K bx X ω

/-- Standing hypotheses on the kernel `K` of Lemma 4.1 (`lem:continuous-entropy-partition`):
bounded measurable, symmetric, centered, nonnegative quadratic form (on bounded measurable
functions), and the entropy–energy inequality `eq:continuous-entropy-assumption` (4.1) with
constant `B > 0`, required only for bounded measurable probability densities. -/
structure KHyp (μE : Measure E) (K : E → E → ℝ) (CK B : ℝ) : Prop where
  meas : Measurable (uncurry K)
  symm : ∀ x y, K x y = K y x
  bdd : ∀ x y, |K x y| ≤ CK
  /-- `∫ K(x,y) dμ(y) = 0`. -/
  centered : ∀ x, ∫ y, K x y ∂μE = 0
  /-- `T_K` is nonnegative. -/
  pos : ∀ f : E → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → 0 ≤ energy μE K f f
  B_pos : 0 < B
  /-- Eq. (4.1): `H(ρμ | μ) ≥ (B/2)⟨ρ − 1, T_K(ρ − 1)⟩` for bounded densities `ρ`. -/
  entropy : ∀ ρ : E → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) → (∀ x, 0 ≤ ρ x) →
    ∫ x, ρ x ∂μE = 1 →
    (B / 2) * energy μE K (fun x => ρ x - 1) (fun x => ρ x - 1)
      ≤ ∫ x, ρ x * Real.log (ρ x) ∂μE

end Defs

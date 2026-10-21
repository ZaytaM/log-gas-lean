import LogGas.BulkHist
import LogGas.BulkDual

/-!
# Regularized Gaussian coarse estimate (A.7)

Source: `notes/appendixA.tex`, eqs. (A.6), (A.7) `eq:coarse-partition-estimate`; audit E6 A5.

* `measurable_coarse` — the regularized coarse energy is a measurable function of the sample;
* `coarse_exp_bound` — for `0 ≤ t < B`,
  `𝔼 exp((tN/2)·coarse) ≤ (1 − t/B)^{-M/2}`, uniformly in `ε > 0`.

Proof: write `Σ_ε⁻¹ = L Lᵀ`, `Lᵀ Σ_ε L = 1`; then `exp((tN/2) ℓᵀΣ_ε⁻¹ℓ)` is the Gaussian average
of `exp(√(tN) ℓ·(Lγ))`, `ℓ·(Lγ) = N⁻¹∑ T(h_γ)(X_i)` by (A.6); exchange the integrals, factor the
i.i.d. product, bound each factor by `integral_exp_T_le`, and finish with the Gaussian integral.

No deviations from the stated interfaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

variable {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE] {M : ℕ}

private lemma bc_ind_abs (A : Set E) (x : E) : |A.indicator (1 : E → ℝ) x| ≤ 1 := by
  by_cases h : x ∈ A <;> simp [h]

private lemma bc_abs_T {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) {h : E → ℝ} {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (x : E) : |T μE K h x| ≤ |CK| * |C| := by
  unfold T
  have : ‖∫ y, K x y * h y ∂μE‖ ≤ |CK| * |C| * μE.real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hK.bdd x y).trans (le_abs_self _)) ((hC y).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _))
  simpa [Real.norm_eq_abs] using this

private lemma bc_measurable_ell {K : E → E → ℝ} (hK : Measurable (uncurry K))
    (bx : Boxes μE M) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : Fin N → Ω → E)
    (hXm : ∀ i, Measurable (X i)) (a : Fin M) :
    Measurable (fun ω => ell μE K bx X ω a) := by
  show Measurable (fun ω => empPair μE K ((bx.A a).indicator 1) X ω)
  unfold empPair
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_T K hK _ (measurable_one.indicator (bx.meas a))).comp (hXm i))

private lemma bc_abs_ell {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B)
    (bx : Boxes μE M) {Ω : Type*} {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Ω → E) (ω : Ω)
    (a : Fin M) : |ell μE K bx X ω a| ≤ |CK| := by
  show |empPair μE K ((bx.A a).indicator 1) X ω| ≤ |CK|
  unfold empPair
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
  have h1 : |∑ i, T μE K ((bx.A a).indicator 1) (X i ω)| ≤ N * |CK| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |T μE K ((bx.A a).indicator 1) (X i ω)| ≤ ∑ _i : Fin N, |CK| * |(1 : ℝ)| :=
          Finset.sum_le_sum fun i _ => bc_abs_T hK (bc_ind_abs (bx.A a)) _
      _ = N * |CK| := by simp
  calc 1 / (N : ℝ) * |∑ i, T μE K ((bx.A a).indicator 1) (X i ω)|
      ≤ 1 / (N : ℝ) * (N * |CK|) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = |CK| := by field_simp

private lemma bc_dot_bound (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) (R : ℝ)
    (hv : ∀ a, |v a| ≤ R) : |v ⬝ᵥ A *ᵥ v| ≤ ∑ a, ∑ b, R * (|A a b| * R) := by
  simp only [dotProduct, Matrix.mulVec]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  calc |v a| * |∑ b, A a b * v b| ≤ R * ∑ b, |A a b| * R := by
        refine mul_le_mul (hv a) ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun b _ => ?_)) (abs_nonneg _) ((abs_nonneg _).trans (hv a))
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv b) (abs_nonneg _)
    _ = ∑ b, R * (|A a b| * R) := by rw [Finset.mul_sum]

/-- The regularized coarse energy is measurable in the sample. -/
theorem measurable_coarse (K : E → E → ℝ) (hK : Measurable (uncurry K)) (bx : Boxes μE M)
    (ε : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : Fin N → Ω → E)
    (hXm : ∀ i, Measurable (X i)) : Measurable (coarse μE K bx ε X) := by
  have hell := bc_measurable_ell (μE := μE) hK bx X hXm
  show Measurable (fun ω => ell μE K bx X ω ⬝ᵥ (gramReg μE K bx ε)⁻¹ *ᵥ ell μE K bx X ω)
  simp only [dotProduct, Matrix.mulVec]
  exact Finset.measurable_sum _ fun a _ => (hell a).mul
    (Finset.measurable_sum _ fun b _ => (hell b).const_mul _)

/-- Eq. `eq:coarse-partition-estimate` (A.7), regularized. -/
theorem coarse_exp_bound {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) (bx : Boxes μE M)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 1 ≤ N) (X : Fin N → Ω → E) (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X μ)
    (hXl : ∀ i, μ.map (X i) = μE) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht0 : 0 ≤ t) (htB : t < B) :
    Integrable (fun ω => Real.exp ((t * N / 2) * coarse μE K bx ε X ω)) μ ∧
      ∫ ω, Real.exp ((t * N / 2) * coarse μE K bx ε X ω) ∂μ ≤ (1 - t / B) ^ (-(M : ℝ) / 2) := by
  classical
  have hB := hK.B_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨G, hGdef⟩ : ∃ G, G = gramReg μE K bx ε := ⟨_, rfl⟩
  have hGpd : G.PosDef := by
    rw [hGdef]
    exact posDef_add_smul_one (gram μE K bx) (gram_posSemidef hK bx) ε hε
  obtain ⟨L, hLL, hLG⟩ := exists_sqrt_inv G hGpd
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (t * N) := ⟨_, rfl⟩
  have hs2 : s * s = t * N := by
    rw [hs]; exact Real.mul_self_sqrt (by positivity)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Ω → Fin M → ℝ, ∀ ω, ℓ ω = ell μE K bx X ω := ⟨_, fun _ => rfl⟩
  have hℓm : ∀ a, Measurable (fun ω => ℓ ω a) := by
    intro a
    simp only [hℓ]
    exact bc_measurable_ell hK.meas bx X hXm a
  have hℓb : ∀ ω a, |ℓ ω a| ≤ |CK| := fun ω a => by rw [hℓ]; exact bc_abs_ell hK bx hN X ω a
  have hcoarse : ∀ ω, coarse μE K bx ε X ω = ℓ ω ⬝ᵥ G⁻¹ *ᵥ ℓ ω := by
    intro ω; rw [hℓ, hGdef]; rfl
  obtain ⟨F, hF⟩ : ∃ F : Ω → (Fin M → ℝ) → ℝ,
      ∀ ω g, F ω g = Real.exp ((s • ℓ ω) ⬝ᵥ (L *ᵥ g)) := ⟨_, fun _ _ => rfl⟩
  -- the Gaussian average of F ω is exp((tN/2) coarse ω)
  have hkey : ∀ ω, ∫ g, F ω g ∂(stdGauss M) = Real.exp ((t * N / 2) * coarse μE K bx ε X ω) := by
    intro ω
    simp only [hF]
    rw [gaussian_mgf_linear]
    congr 1
    have h2 : (Lᵀ *ᵥ ℓ ω) ⬝ᵥ (Lᵀ *ᵥ ℓ ω) = ℓ ω ⬝ᵥ G⁻¹ *ᵥ ℓ ω := by
      rw [← hLL, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (ℓ ω) L, Matrix.mulVec_transpose]
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, h2,
      hcoarse]
    have : s * (s * (ℓ ω ⬝ᵥ G⁻¹ *ᵥ ℓ ω)) = (s * s) * (ℓ ω ⬝ᵥ G⁻¹ *ᵥ ℓ ω) := by ring
    rw [this, hs2]; ring
  have hkey_int : ∀ ω, Integrable (fun g => F ω g) (stdGauss M) := by
    intro ω
    refine Integrable.of_integral_ne_zero ?_
    rw [hkey]; exact (Real.exp_pos _).ne'
  -- boundedness / integrability of the coarse exponential
  have hcm : Measurable (coarse μE K bx ε X) := measurable_coarse K hK.meas bx ε X hXm
  have hCb : ∀ ω, |coarse μE K bx ε X ω| ≤ ∑ a, ∑ b, |CK| * (|G⁻¹ a b| * |CK|) := by
    intro ω; rw [hcoarse]; exact bc_dot_bound G⁻¹ (ℓ ω) |CK| (hℓb ω)
  have hexpint : Integrable (fun ω => Real.exp ((t * N / 2) * coarse μE K bx ε X ω)) μ := by
    refine Integrable.of_bound (C := Real.exp (|t * N / 2| * ∑ a, ∑ b, |CK| * (|G⁻¹ a b| * |CK|)))
      ((Real.measurable_exp.comp (hcm.const_mul _)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc t * N / 2 * coarse μE K bx ε X ω ≤ |t * N / 2 * coarse μE K bx ε X ω| := le_abs_self _
      _ = |t * N / 2| * |coarse μE K bx ε X ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hCb ω) (abs_nonneg _)
  refine ⟨hexpint, ?_⟩
  -- joint measurability
  have hFm : Measurable (uncurry F) := by
    have : uncurry F = fun p : Ω × (Fin M → ℝ) =>
        Real.exp (∑ a, (s * ℓ p.1 a) * ∑ b, L a b * p.2 b) := by
      funext p
      simp only [uncurry, hF, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul]
    rw [this]
    refine Real.measurable_exp.comp (Finset.measurable_sum _ fun a _ => ?_)
    exact (measurable_const.mul ((hℓm a).comp measurable_fst)).mul
      (Finset.measurable_sum _ fun b _ =>
        measurable_const.mul ((measurable_pi_apply b).comp measurable_snd))
  have hFint : Integrable (uncurry F) (μ.prod (stdGauss M)) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ω => hkey_int ω, ?_⟩
    have : (fun ω => ∫ g, ‖uncurry F (ω, g)‖ ∂(stdGauss M))
        = fun ω => Real.exp ((t * N / 2) * coarse μE K bx ε X ω) := by
      funext ω
      rw [← hkey ω]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [uncurry, Real.norm_eq_abs, hF]
      exact abs_of_pos (Real.exp_pos _)
    rw [this]; exact hexpint
  have hswap := integral_integral_swap hFint
  -- the inner (sample) integral bound
  have hinner : ∀ g, ∫ ω, F ω g ∂μ ≤ Real.exp ((t / B / 2) * (g ⬝ᵥ g)) := by
    intro g
    obtain ⟨c0, hc0⟩ : ∃ c0 : Fin M → ℝ, c0 = L *ᵥ g := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c' : Fin M → ℝ, c' = ((s / N) • c0) := ⟨_, rfl⟩
    have hcell : ∀ ω, F ω g = Real.exp (∑ i, T μE K (cellFun bx c') (X i ω)) := by
      intro ω
      rw [hF, ← hc0]
      congr 1
      have h3 := empPair_cellFun hK.meas hK.bdd bx c' X ω
      unfold empPair at h3
      have h4 : ∑ i, T μE K (cellFun bx c') (X i ω) = N * (c' ⬝ᵥ ell μE K bx X ω) := by
        rw [← h3]; field_simp
      rw [h4, ← hℓ, hc', smul_dotProduct, smul_dotProduct, dotProduct_comm c0]
      simp only [smul_eq_mul]
      field_simp
    have hCbd : ∀ x, |cellFun bx c' x| ≤ ∑ a, |c' a| := abs_cellFun_le bx c'
    have hTm : Measurable (T μE K (cellFun bx c')) :=
      measurable_T K hK.meas _ (measurable_cellFun bx c')
    have hTb : ∀ x, |T μE K (cellFun bx c') x| ≤ |CK| * |(∑ a, |c' a|)| := bc_abs_T hK hCbd
    simp_rw [hcell]
    rw [iid_exp_sum μ μE X hXm hXi hXl (T μE K (cellFun bx c')) hTm _ hTb]
    obtain ⟨hint, hle⟩ := integral_exp_T_le hK (cellFun bx c') (measurable_cellFun bx c') _ hCbd
    rw [energy_cellFun hK.meas hK.bdd] at hle
    -- c0 ⬝ G c0 = g ⬝ g
    have e1 : Lᵀ *ᵥ (G *ᵥ (L *ᵥ g)) = g := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hLG, Matrix.one_mulVec]
    have e2 : c0 ⬝ᵥ G *ᵥ c0 = g ⬝ᵥ g := by
      rw [hc0, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, e1]
    have e3 : c0 ⬝ᵥ G *ᵥ c0 = c0 ⬝ᵥ gram μE K bx *ᵥ c0 + ε * (c0 ⬝ᵥ c0) := by
      rw [hGdef]
      simp [gramReg, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec]
    have e4 : 0 ≤ c0 ⬝ᵥ c0 := Finset.sum_nonneg fun a _ => mul_self_nonneg _
    have e5 : c' ⬝ᵥ gram μE K bx *ᵥ c' = (s / N) ^ 2 * (c0 ⬝ᵥ gram μE K bx *ᵥ c0) := by
      rw [hc', Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
      simp only [smul_eq_mul]; ring
    have e6 : c0 ⬝ᵥ gram μE K bx *ᵥ c0 ≤ g ⬝ᵥ g := by
      nlinarith [mul_nonneg hε.le e4]
    have e7 : (s / N) ^ 2 = t / N := by
      rw [div_pow, sq, hs2]; field_simp
    have e8 : c' ⬝ᵥ gram μE K bx *ᵥ c' ≤ t / N * (g ⬝ᵥ g) := by
      rw [e5, e7]
      exact mul_le_mul_of_nonneg_left e6 (by positivity)
    calc (∫ x, Real.exp (T μE K (cellFun bx c') x) ∂μE) ^ N
        ≤ (Real.exp (c' ⬝ᵥ gram μE K bx *ᵥ c' / (2 * B))) ^ N :=
          pow_le_pow_left₀ (integral_nonneg fun x => (Real.exp_pos _).le) hle N
      _ = Real.exp (N * (c' ⬝ᵥ gram μE K bx *ᵥ c' / (2 * B))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((t / B / 2) * (g ⬝ᵥ g)) := by
          refine Real.exp_le_exp.2 ?_
          have : (N : ℝ) * (c' ⬝ᵥ gram μE K bx *ᵥ c' / (2 * B))
              ≤ N * (t / N * (g ⬝ᵥ g) / (2 * B)) := by
            refine mul_le_mul_of_nonneg_left ?_ hNpos.le
            exact div_le_div_of_nonneg_right e8 (by positivity)
          refine this.trans (le_of_eq ?_)
          field_simp
  -- Gaussian integral
  have hq := gaussian_quadratic_integral M (t / B) (by positivity)
    (by rw [div_lt_one hB]; exact htB)
  have hgi : Integrable (fun g : Fin M → ℝ => Real.exp ((t / B / 2) * (g ⬝ᵥ g))) (stdGauss M) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hq]
    exact (Real.rpow_pos_of_pos (by rw [sub_pos, div_lt_one hB]; exact htB) _).ne'
  calc ∫ ω, Real.exp ((t * N / 2) * coarse μE K bx ε X ω) ∂μ
      = ∫ ω, ∫ g, F ω g ∂(stdGauss M) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (hkey ω).symm
    _ = ∫ g, ∫ ω, F ω g ∂μ ∂(stdGauss M) := hswap
    _ ≤ ∫ g, Real.exp ((t / B / 2) * (g ⬝ᵥ g)) ∂(stdGauss M) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) hgi
          (Filter.Eventually.of_forall hinner)
        exact integral_nonneg fun ω => by rw [hF]; exact (Real.exp_pos _).le
    _ = (1 - t / B) ^ (-(M : ℝ) / 2) := hq

end LogGas.Bulk

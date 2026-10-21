import LogGas.Bulk

/-!
# Appendix A, step 1: pairing identities for cell functions

Source: `notes/appendixA.tex`, eqs. `eq:empirical-histogram-splitting` (A.1) and
`eq:coarse-gaussian-pairing` (A.6); audit DEVIATIONS E6 (A1, A4).

* `histogram_box` — `∫_{A_a} f_L dμ = n_a / N`, i.e. `ν_N(A_a) = 0` in (A.1);
* `measurable_cellFun`, `abs_cellFun_le` — basic properties of `cellFun`;
* `T_cellFun`, `empPair_cellFun`, `energy_cellFun` — the pairing `⟨h, T μ_N⟩ = c · ℓ` of (A.6)
  and the energy form `⟨h, T h⟩ = c · Σ c` for cell functions `h = cellFun bx c`;
* `gram_posSemidef` — the cell Gram matrix is positive semidefinite.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

variable {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE]
  {M N : ℕ} {Ω : Type*}

private theorem bh_cellFun_eq (bx : Boxes μE M) (c : Fin M → ℝ) (x : E) :
    cellFun bx c x = ∑ a, c a * (bx.A a).indicator (1 : E → ℝ) x := by
  unfold cellFun
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : x ∈ bx.A a <;> simp [Set.indicator, h]

private theorem bh_ind_meas (bx : Boxes μE M) (a : Fin M) :
    Measurable ((bx.A a).indicator (1 : E → ℝ)) :=
  measurable_one.indicator (bx.meas a)

private theorem bh_ind_abs (bx : Boxes μE M) (a : Fin M) (x : E) :
    |(bx.A a).indicator (1 : E → ℝ) x| ≤ 1 := by
  by_cases h : x ∈ bx.A a <;> simp [Set.indicator, h]

private theorem bh_integrable {f : E → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f μE :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)

/-- Eq. (A.1): the histogram `f_L` has `∫_{A_a} f_L = n_a / N`. -/
theorem histogram_box (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) (a : Fin M) :
    ∫ x in bx.A a, hist X bx ω x ∂μE = (occupancy X (bx.A a) ω : ℝ) / N := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Fin.pos a
  have hvol := bx.real_vol a
  have hpt : ∀ x, hist X bx ω x
      = ∑ b, histCoef X bx ω b * (bx.A b).indicator (1 : E → ℝ) x := fun x =>
    bh_cellFun_eq bx _ x
  simp_rw [hpt]
  have hint : ∀ b, Integrable (fun x => histCoef X bx ω b * (bx.A b).indicator (1 : E → ℝ) x)
      (μE.restrict (bx.A a)) := fun b =>
    ((bh_integrable (bh_ind_meas bx b) 1 (bh_ind_abs bx b)).const_mul _).restrict
  rw [integral_finsetSum _ (fun b _ => hint b)]
  have hb : ∀ b, ∫ x in bx.A a, histCoef X bx ω b * (bx.A b).indicator (1 : E → ℝ) x ∂μE
      = if b = a then histCoef X bx ω a * (1 / M) else 0 := by
    intro b
    rw [integral_const_mul]
    by_cases hba : b = a
    · subst hba
      rw [if_pos rfl]
      congr 1
      rw [setIntegral_congr_fun (bx.meas b) (g := fun _ => (1 : ℝ))
        (fun x hx => by simp [Set.indicator, hx])]
      simp [Measure.real, bx.vol b]
    · rw [if_neg hba]
      have : ∫ x in bx.A a, (bx.A b).indicator (1 : E → ℝ) x ∂μE = 0 := by
        rw [setIntegral_congr_fun (bx.meas a) (g := fun _ => (0 : ℝ))
          (fun x hx => by
            have : x ∉ bx.A b := fun hxb =>
              (Set.disjoint_left.mp (bx.disj hba) hxb) hx
            simp [Set.indicator, this])]
        simp
      rw [this, mul_zero]
  simp_rw [hb]
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ a)]
  unfold histCoef
  field_simp

theorem measurable_cellFun (bx : Boxes μE M) (c : Fin M → ℝ) : Measurable (cellFun bx c) := by
  unfold cellFun
  exact Finset.measurable_sum _ fun a _ => measurable_const.indicator (bx.meas a)

theorem abs_cellFun_le (bx : Boxes μE M) (c : Fin M → ℝ) (x : E) :
    |cellFun bx c x| ≤ ∑ a, |c a| := by
  rw [bh_cellFun_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  calc |c a| * |(bx.A a).indicator (1 : E → ℝ) x| ≤ |c a| * 1 :=
        mul_le_mul_of_nonneg_left (bh_ind_abs bx a x) (abs_nonneg _)
    _ = |c a| := mul_one _

section Kernel

variable {K : E → E → ℝ} (hK : Measurable (uncurry K)) {CK : ℝ} (hKb : ∀ x y, |K x y| ≤ CK)

include hK hKb

private theorem bh_slice_int (x : E) {h : E → ℝ} (hh : Measurable h) (C : ℝ)
    (hC : ∀ y, |h y| ≤ C) : Integrable (fun y => K x y * h y) μE := by
  refine bh_integrable ((hK.comp measurable_prodMk_left).mul hh) (CK * C) fun y => ?_
  rw [abs_mul]
  exact mul_le_mul (hKb x y) (hC y) (abs_nonneg _) ((abs_nonneg _).trans (hKb x y))

private theorem bh_T_meas {h : E → ℝ} (hh : Measurable h) : Measurable (T μE K h) := by
  unfold T
  have : Measurable (fun p : E × E => K p.1 p.2 * h p.2) :=
    hK.mul (hh.comp measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right').measurable

private theorem bh_T_abs {h : E → ℝ} (C : ℝ) (hC : ∀ y, |h y| ≤ C) (x : E) :
    |T μE K h x| ≤ CK * C := by
  unfold T
  have := norm_integral_le_of_norm_le_const (μ := μE) (f := fun y => K x y * h y)
    (C := CK * C) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hKb x y) (hC y) (abs_nonneg _) ((abs_nonneg _).trans (hKb x y)))
  simpa [Real.norm_eq_abs] using this

theorem T_cellFun (bx : Boxes μE M) (c : Fin M → ℝ) (x : E) :
    T μE K (cellFun bx c) x = ∑ a, c a * T μE K ((bx.A a).indicator 1) x := by
  unfold T
  have hpt : ∀ y, K x y * cellFun bx c y
      = ∑ a, c a * (K x y * (bx.A a).indicator (1 : E → ℝ) y) := fun y => by
    rw [bh_cellFun_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ =>
    (bh_slice_int hK hKb x (bh_ind_meas bx a) 1 (bh_ind_abs bx a)).const_mul _)]
  exact Finset.sum_congr rfl fun a _ => integral_const_mul _ _

theorem empPair_cellFun (bx : Boxes μE M) (c : Fin M → ℝ) (X : Fin N → Ω → E) (ω : Ω) :
    empPair μE K (cellFun bx c) X ω = c ⬝ᵥ ell μE K bx X ω := by
  unfold empPair ell
  simp_rw [T_cellFun hK hKb bx c]
  rw [Finset.sum_comm, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold empPair
  rw [← Finset.mul_sum]
  ring

private theorem bh_energy_eq {f g : E → ℝ} (hf : Measurable f) (Cf : ℝ) (hCf : ∀ x, |f x| ≤ Cf)
    (hg : Measurable g) (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg) :
    energy μE K f g = ∫ x, f x * T μE K g x ∂μE := by
  unfold energy T
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)

private theorem bh_energy_ind (bx : Boxes μE M) (a b : Fin M) :
    energy μE K ((bx.A a).indicator 1) ((bx.A b).indicator 1)
      = ∫ x, (bx.A a).indicator (1 : E → ℝ) x * T μE K ((bx.A b).indicator 1) x ∂μE :=
  bh_energy_eq hK hKb (bh_ind_meas bx a) 1 (bh_ind_abs bx a) (bh_ind_meas bx b) 1
    (bh_ind_abs bx b)

theorem energy_cellFun (bx : Boxes μE M) (c : Fin M → ℝ) :
    energy μE K (cellFun bx c) (cellFun bx c) = c ⬝ᵥ (gram μE K bx *ᵥ c) := by
  have hCc : ∀ x, |cellFun bx c x| ≤ ∑ a, |c a| := abs_cellFun_le bx c
  rw [bh_energy_eq hK hKb (measurable_cellFun bx c) _ hCc (measurable_cellFun bx c) _ hCc]
  have hint : ∀ a b, Integrable (fun x => c a * (c b *
      ((bx.A a).indicator (1 : E → ℝ) x * T μE K ((bx.A b).indicator 1) x))) μE := by
    intro a b
    refine (bh_integrable (C := CK * 1) ((bh_ind_meas bx a).mul
      (bh_T_meas hK hKb (bh_ind_meas bx b))) ?_).const_mul _ |>.const_mul _
    intro x
    simp only [Pi.mul_apply]
    rw [abs_mul]
    calc |(bx.A a).indicator (1 : E → ℝ) x| * |T μE K ((bx.A b).indicator 1) x|
        ≤ 1 * (CK * 1) := mul_le_mul (bh_ind_abs bx a x)
          (bh_T_abs hK hKb 1 (bh_ind_abs bx b) x) (abs_nonneg _) zero_le_one
      _ = CK * 1 := one_mul _
  have hpt : ∀ x, cellFun bx c x * T μE K (cellFun bx c) x
      = ∑ a, ∑ b, c a * (c b *
        ((bx.A a).indicator (1 : E → ℝ) x * T μE K ((bx.A b).indicator 1) x)) := by
    intro x
    rw [T_cellFun hK hKb bx c x, bh_cellFun_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hint a b)]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hint a b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_const_mul]
  simp only [gram, Matrix.of_apply]
  rw [bh_energy_ind hK hKb bx a b]
  ring

end Kernel

theorem gram_posSemidef {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) (bx : Boxes μE M) :
    (gram μE K bx).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun c => ?_⟩
  · -- Hermitian: transpose-symmetric, via Fubini
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext a b
    simp only [Matrix.transpose_apply, gram, Matrix.of_apply, energy]
    have hint : Integrable (uncurry fun x y => K x y * (bx.A a).indicator (1 : E → ℝ) x *
        (bx.A b).indicator (1 : E → ℝ) y) (μE.prod μE) := by
      refine Integrable.of_bound (C := CK * 1 * 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact ((hK.meas.mul ((bh_ind_meas bx a).comp measurable_fst)).mul
          ((bh_ind_meas bx b).comp measurable_snd)).aestronglyMeasurable
      · simp only [uncurry, Real.norm_eq_abs, abs_mul]
        have h0 : 0 ≤ CK := (abs_nonneg _).trans (hK.bdd p.1 p.2)
        exact mul_le_mul (mul_le_mul (hK.bdd _ _) (bh_ind_abs bx a _) (abs_nonneg _) h0)
          (bh_ind_abs bx b _) (abs_nonneg _) (by positivity)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hK.symm y x]; ring
  · have hc := hK.pos (cellFun bx c) (measurable_cellFun bx c) ⟨_, abs_cellFun_le bx c⟩
    rw [energy_cellFun hK.meas hK.bdd] at hc
    simpa using hc

end LogGas.Bulk

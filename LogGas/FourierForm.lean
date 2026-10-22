import LogGas.TorusBase

/-!
# Quadratic forms of translation-invariant kernels via Parseval

Source: `notes/sec2-cutoff.tex` (2.2), `eq:compact-split-fourier-order` ("both centered parts PSD",
"energy form bounded by that of g"). For `K ∈ L¹(T^d)` and bounded measurable `f`:
* `coeff_conv`: `coeff (K * f) k = coeff K k * coeff f k`;
* `quadratic_hasSum`: `⟨f, K * f⟩ = ∑ₖ coeff K k * |coeff f k|²` (Parseval on `L²`);
* `quadratic_nonneg_of_coeff`, `quadratic_mono_of_coeff`: positivity / monotonicity from the
  Fourier coefficients.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LogGas.Fourier
open LogGas.Torus LogGas.Spec

section Aux

noncomputable local instance fourierform_unitCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

private theorem ff_negChar_eq {d : ℕ} (k : Fin d → ℤ) :
    negChar k = ⇑(UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)) := rfl

private theorem ff_negChar_cont {d : ℕ} (k : Fin d → ℤ) : Continuous (negChar k) := by
  rw [ff_negChar_eq]; exact ContinuousMap.continuous _

private theorem ff_fourier_norm (n : ℤ) (z : AddCircle (1 : ℝ)) : ‖fourier n z‖ = 1 := by
  have h : fourier n z * fourier (-n) z = 1 := by
    rw [← fourier_add]; simp
  have h2 : ‖fourier n z‖ * ‖fourier (-n) z‖ = 1 := by rw [← norm_mul, h]; simp
  have h3 : ‖fourier n z‖ ≤ 1 := by
    simpa using (fourier n : C(AddCircle (1 : ℝ), ℂ)).norm_coe_le_norm z |>.trans
      (le_of_eq (fourier_norm n))
  have h4 : ‖fourier (-n) z‖ ≤ 1 := by
    simpa using (fourier (-n) : C(AddCircle (1 : ℝ), ℂ)).norm_coe_le_norm z |>.trans
      (le_of_eq (fourier_norm (-n)))
  nlinarith [norm_nonneg (fourier n z), norm_nonneg (fourier (-n) z)]

private theorem ff_negChar_norm {d : ℕ} (k : Fin d → ℤ) (x : T d) : ‖negChar k x‖ = 1 := by
  unfold negChar
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => ff_fourier_norm _ _

private theorem ff_negChar_add {d : ℕ} (k : Fin d → ℤ) (x y : T d) :
    negChar k (x + y) = negChar k x * negChar k y := by
  unfold negChar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  simp_rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]


private theorem ff_integrable_sub {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d)) :
    Integrable (fun z : T d × T d => K (z.1 - z.2)) ((unif d).prod (unif d)) :=
  (measurePreserving_sub d).integrable_comp_of_integrable hK

private theorem ff_integrable_H {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (f : T d → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) (k : Fin d → ℤ) :
    Integrable (fun z : T d × T d => negChar k z.1 * ((K (z.1 - z.2) * f z.2 : ℝ) : ℂ))
      ((unif d).prod (unif d)) := by
  have h1 := ff_integrable_sub K hK
  refine Integrable.mono' (h1.norm.mul_const C) ?_ ?_
  · refine ((ff_negChar_cont k).comp continuous_fst).aestronglyMeasurable.mul ?_
    refine Complex.continuous_ofReal.comp_aestronglyMeasurable ?_
    exact h1.aestronglyMeasurable.mul (hf.comp measurable_snd).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul, ff_negChar_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfC _) (abs_nonneg _) |>.trans_eq (by simp)

/-- `coeff_conv`: Fourier coefficients of a convolution multiply. -/
theorem coeff_conv {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (f : T d → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) (k : Fin d → ℤ) :
    coeff (fun x => ∫ y, K (x - y) * f y ∂unif d) k = coeff K k * coeff f k := by
  have hH := ff_integrable_H K hK f hf C hfC k
  have step1 : coeff (fun x => ∫ y, K (x - y) * f y ∂unif d) k
      = ∫ x, ∫ y, negChar k x * ((K (x - y) * f y : ℝ) : ℂ) ∂unif d ∂unif d := by
    unfold coeff
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_const_mul]
    congr 1
    exact integral_ofReal.symm
  rw [step1]
  rw [integral_integral_swap (f := fun x y => negChar k x * ((K (x - y) * f y : ℝ) : ℂ)) hH]
  have step2 : ∀ y, ∫ x, negChar k x * ((K (x - y) * f y : ℝ) : ℂ) ∂unif d
      = negChar k y * (f y : ℂ) * coeff K k := by
    intro y
    have := integral_add_right_eq_self (μ := unif d)
      (fun x => negChar k x * ((K (x - y) * f y : ℝ) : ℂ)) y
    rw [← this]
    unfold coeff
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [add_sub_cancel_right, ff_negChar_add, Complex.ofReal_mul]
    ring
  simp_rw [step2]
  unfold coeff
  rw [integral_mul_const]
  ring


private theorem ff_volume_eq (d : ℕ) : (volume : Measure (UnitAddTorus (Fin d))) = unif d := rfl

private theorem ff_conv_bound {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (f : T d → ℝ) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) (x : T d) :
    |∫ y, K (x - y) * f y ∂unif d| ≤ C * ∫ y, |K y| ∂unif d := by
  have hi : Integrable (fun y => |K (x - y)|) (unif d) := (hK.comp_sub_left x).abs
  calc |∫ y, K (x - y) * f y ∂unif d| = ‖∫ y, K (x - y) * f y ∂unif d‖ := rfl
    _ ≤ ∫ y, |K (x - y)| * C ∂unif d := by
        refine norm_integral_le_of_norm_le (hi.mul_const C) (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hfC y) (abs_nonneg _)
    _ = C * ∫ y, |K y| ∂unif d := by
        rw [integral_mul_const, mul_comm]
        congr 1
        exact integral_sub_left_eq_self (fun y => |K y|) (unif d) x

private theorem ff_conv_aesm {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (f : T d → ℝ) (hf : Measurable f) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) * f y ∂unif d) (unif d) := by
  have h1 := ff_integrable_sub K hK
  have : AEStronglyMeasurable (fun z : T d × T d => K (z.1 - z.2) * f z.2)
      ((unif d).prod (unif d)) :=
    h1.aestronglyMeasurable.mul (hf.comp measurable_snd).aestronglyMeasurable
  exact this.integral_prod_right'

private theorem ff_memLp {d : ℕ} (g : T d → ℝ) (hg : AEStronglyMeasurable g (unif d)) (M : ℝ)
    (hM : ∀ x, |g x| ≤ M) : MemLp (fun x => (g x : ℂ)) 2 (unif d) := by
  refine MemLp.of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable hg) M
    (Filter.Eventually.of_forall fun x => ?_)
  simpa [Complex.norm_real] using hM x

private theorem ff_mFourierCoeff_toLp {d : ℕ} (g : T d → ℝ)
    (hmem : MemLp (fun x => (g x : ℂ)) 2 (unif d)) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (hmem.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) k
      = coeff g k := by
  unfold UnitAddTorus.mFourierCoeff coeff
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hmem] with x hx
  rw [hx]
  rfl


/-- Parseval for the quadratic form of a translation-invariant kernel. -/
theorem quadratic_hasSum {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (f : T d → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    HasSum (fun k => coeff K k * ((Complex.normSq (coeff f k) : ℝ) : ℂ))
      ((quadratic (fun x y => K (x - y)) f : ℝ) : ℂ) := by
  set F : T d → ℝ := fun x => ∫ y, K (x - y) * f y ∂unif d with hF
  have hFm : MemLp (fun x => (F x : ℂ)) 2 (unif d) :=
    ff_memLp F (ff_conv_aesm K hK f hf) _ (ff_conv_bound K hK f C hfC)
  have hfm : MemLp (fun x => (f x : ℂ)) 2 (unif d) :=
    ff_memLp f hf.aestronglyMeasurable C hfC
  have hP := UnitAddTorus.hasSum_prod_mFourierCoeff
    (hfm.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))))
    (hFm.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))))
  have e1 := ff_mFourierCoeff_toLp f hfm
  have e2 := ff_mFourierCoeff_toLp F hFm
  have hval : ∫ t, conj ((hfm.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) t) *
      (hFm.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) t
      = ((quadratic (fun x y => K (x - y)) f : ℝ) : ℂ) := by
    have h1 : ∀ᵐ t ∂unif d, conj ((hfm.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) t) *
        (hFm.toLp _ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) t
        = ((f t * F t : ℝ) : ℂ) := by
      filter_upwards [MemLp.coeFn_toLp hfm, MemLp.coeFn_toLp hFm] with t h1 h2
      rw [h1, h2]
      simp
    refine (integral_congr_ae (μ := unif d) h1).trans ?_
    rw [show (∫ a, ((f a * F a : ℝ) : ℂ) ∂unif d) = ((∫ a, f a * F a ∂unif d : ℝ) : ℂ) from
      integral_ofReal]
    congr 1
    unfold quadratic
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hP2 : HasSum (fun k => conj (coeff f k) * coeff F k)
      ((quadratic (fun x y => K (x - y)) f : ℝ) : ℂ) := by
    rw [← hval]
    convert hP using 3 with k
    all_goals first
      | rfl
      | exact congrArg _ (e1 k).symm
      | exact (e2 k).symm
  refine hP2.congr_fun fun k => ?_
  have hc := coeff_conv K hK f hf C hfC k
  have : coeff F k = coeff K k * coeff f k := hc
  simp only [this]
  rw [Complex.normSq_eq_conj_mul_self]
  ring


private theorem ff_hasSum_re {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (f : T d → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    HasSum (fun k => (coeff K k).re * Complex.normSq (coeff f k))
      (quadratic (fun x y => K (x - y)) f) := by
  have h := (Complex.hasSum_re (quadratic_hasSum K hK f hf C hfC))
  simpa [Complex.re_mul_ofReal] using h

/-- Positivity of the quadratic form from nonnegative Fourier coefficients. -/
theorem quadratic_nonneg_of_coeff {d : ℕ} (K : T d → ℝ) (hK : Integrable K (unif d))
    (hcoef : ∀ k, (coeff K k).im = 0 ∧ 0 ≤ (coeff K k).re)
    (f : T d → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    0 ≤ quadratic (fun x y => K (x - y)) f :=
  HasSum.nonneg (fun k => mul_nonneg (hcoef k).2 (Complex.normSq_nonneg _))
    (ff_hasSum_re K hK f hf C hfC)

/-- Monotonicity of the quadratic form in the Fourier coefficients. -/
theorem quadratic_mono_of_coeff {d : ℕ} (K₁ K₂ : T d → ℝ) (h₁ : Integrable K₁ (unif d))
    (h₂ : Integrable K₂ (unif d))
    (hcoef : ∀ k, (coeff K₁ k).im = 0 ∧ (coeff K₂ k).im = 0 ∧
      (coeff K₁ k).re ≤ (coeff K₂ k).re)
    (f : T d → ℝ) (hf : Measurable f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    quadratic (fun x y => K₁ (x - y)) f ≤ quadratic (fun x y => K₂ (x - y)) f :=
  hasSum_le (fun k => mul_le_mul_of_nonneg_right (hcoef k).2.2 (Complex.normSq_nonneg _))
    (ff_hasSum_re K₁ h₁ f hf C hfC) (ff_hasSum_re K₂ h₂ f hf C hfC)

end Aux
end LogGas.Fourier

import LogGas.TorusBase

/-!
# L¹ Fourier uniqueness on the torus

Source: `PaperChallenge.lean` (`IsLogKernel` docstring); audit deviations C2, C4, E11, G6.
If `f ∈ L¹(𝕋^d)` has all Fourier coefficients zero then `f = 0` a.e.; hence two integrable
real functions with equal Fourier coefficients agree a.e.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace LogGas.Fourier
open LogGas.Torus

private theorem fu_int_mul {d : ℕ} (f : T d → ℝ) (hf : Integrable f (unif d))
    (φ : C(T d, ℂ)) : Integrable (fun x => φ x * (f x : ℂ)) (unif d) := by
  have hf' : Integrable (fun x => (f x : ℂ)) (unif d) := hf.ofReal
  have : Integrable (fun x => (f x : ℂ) * φ x) (unif d) :=
    hf'.mul_bdd (c := ‖φ‖) φ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => φ.norm_coe_le_norm x)
  simpa [mul_comm] using this

theorem integral_mul_eq_zero_of_coeff {d : ℕ} (f : T d → ℝ) (hf : Integrable f (unif d))
    (h : ∀ k, coeff f k = 0) (φ : C(T d, ℂ)) :
    ∫ x, φ x * (f x : ℂ) ∂unif d = 0 := by
  let L : C(T d, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ x, φ x * (f x : ℂ) ∂unif d
      map_add' := fun a b => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (fu_int_mul f hf a) (fu_int_mul f hf b)
      map_smul' := fun c a => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hL : ∀ φ, ‖L φ‖ ≤ (∫ x, ‖f x‖ ∂unif d) * ‖φ‖ := by
    intro φ
    show ‖∫ x, φ x * (f x : ℂ) ∂unif d‖ ≤ _
    calc ‖∫ x, φ x * (f x : ℂ) ∂unif d‖ ≤ ∫ x, ‖φ x * (f x : ℂ)‖ ∂unif d :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖φ‖ * ‖f x‖ ∂unif d := by
          refine integral_mono (fu_int_mul f hf φ).norm (hf.norm.const_mul _) fun x => ?_
          simp only [norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
      _ = _ := by rw [integral_const_mul, mul_comm]
  let Lc : C(T d, ℂ) →L[ℂ] ℂ := L.mkContinuous _ hL
  have hclosed : IsClosed (LinearMap.ker L : Set C(T d, ℂ)) :=
    (ContinuousLinearMap.isClosed_ker Lc)
  have hspan : Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d))) ≤
      LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    have := h (-n)
    simp only [coeff, negChar] at this
    show L _ = 0
    simpa [L, UnitAddTorus.mFourier] using this
  have htop := UnitAddTorus.span_mFourier_closure_eq_top (d := Fin d)
  have hmem : φ ∈ (Submodule.span ℂ
      (Set.range (UnitAddTorus.mFourier (d := Fin d)))).topologicalClosure := by
    rw [htop]; trivial
  have := Submodule.topologicalClosure_minimal _ hspan hclosed hmem
  exact this

private theorem fu_int_real {d : ℕ} (F : T d → ℝ) (hF : Integrable F (unif d))
    (g : T d →ᵇ ℝ) : Integrable (fun x => g x * F x) (unif d) := by
  let φ : C(T d, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩
  have := (fu_int_mul F hF φ).re
  simpa [φ] using this

theorem ae_eq_zero_of_coeff_eq_zero {d : ℕ} (f : T d → ℝ) (hf : Integrable f (unif d))
    (h : ∀ k, coeff f k = 0) : f =ᵐ[unif d] 0 := by
  have hreal : ∀ g : T d →ᵇ ℝ, ∫ x, g x * f x ∂unif d = 0 := by
    intro g
    let φ : C(T d, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩
    have := integral_mul_eq_zero_of_coeff f hf h φ
    have h2 : ∫ x, ((g x * f x : ℝ) : ℂ) ∂unif d = 0 := by simpa [φ] using this
    rw [integral_complex_ofReal] at h2
    exact_mod_cast h2
  have hpos : AEMeasurable (fun x => ENNReal.ofReal (f x)) (unif d) :=
    hf.aemeasurable.ennreal_ofReal
  have hneg : AEMeasurable (fun x => ENNReal.ofReal (-f x)) (unif d) :=
    hf.aemeasurable.neg.ennreal_ofReal
  haveI : IsFiniteMeasure ((unif d).withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  haveI : IsFiniteMeasure ((unif d).withDensity fun x => ENNReal.ofReal (-f x)) :=
    isFiniteMeasure_withDensity hf.neg.lintegral_lt_top.ne
  have heq : (unif d).withDensity (fun x => ENNReal.ofReal (f x)) =
      (unif d).withDensity (fun x => ENNReal.ofReal (-f x)) := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    rw [integral_withDensity_eq_integral_toReal_smul₀ hpos
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hneg
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hi1 := fu_int_real _ hf.pos_part g
    have hi2 := fu_int_real _ hf.neg_part g
    have key : ∀ x, g x * (f x)⁺ - g x * (f x)⁻ = g x * f x := by
      intro x
      rw [← mul_sub, posPart_sub_negPart]
    have h3 := hreal g
    have e1 : (fun x => (ENNReal.ofReal (f x)).toReal • g x) = fun x => g x * (f x)⁺ := by
      ext x; simp [ENNReal.toReal_ofReal', posPart_def, mul_comm]
    have e2 : (fun x => (ENNReal.ofReal (-f x)).toReal • g x) = fun x => g x * (f x)⁻ := by
      ext x; simp [ENNReal.toReal_ofReal', negPart_def, mul_comm]
    rw [e1, e2, ← sub_eq_zero, ← h3]
    exact (integral_sub hi1 hi2).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall key))
  have := (withDensity_eq_iff_of_sigmaFinite hpos hneg).1 heq
  filter_upwards [this] with x hx
  simp only [Pi.zero_apply]
  rcases lt_trichotomy (f x) 0 with h0 | h0 | h0
  · rw [ENNReal.ofReal_of_nonpos h0.le] at hx
    exact absurd hx.symm (ENNReal.ofReal_pos.2 (by linarith)).ne'
  · exact h0
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -f x ≤ 0)] at hx
    exact absurd hx (ENNReal.ofReal_pos.2 h0).ne'

theorem ae_eq_of_coeff_eq {d : ℕ} (f g : T d → ℝ) (hf : Integrable f (unif d))
    (hg : Integrable g (unif d)) (h : ∀ k, coeff f k = coeff g k) : f =ᵐ[unif d] g := by
  have hk : ∀ k, coeff (fun x => f x - g x) k = 0 := by
    intro k
    let φ : C(T d, ℂ) := UnitAddTorus.mFourier (-k)
    have : coeff (fun x => f x - g x) k = coeff f k - coeff g k := by
      simp only [coeff, Complex.ofReal_sub, mul_sub]
      exact integral_sub (fu_int_mul f hf φ) (fu_int_mul g hg φ)
    rw [this, h k, sub_self]
  have := ae_eq_zero_of_coeff_eq_zero _ (hf.sub hg) hk
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end LogGas.Fourier

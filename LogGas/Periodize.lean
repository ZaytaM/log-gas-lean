import LogGas.TorusBase

/-!
# Periodization: functions on `ℝ^d` supported in the ball of radius `1/2` versus the torus

Source: `notes/sec2-cutoff.tex`, (2.1) (the periodized `s_r`; the sum over `m ∈ ℤ^d`
collapses because the support lies in the fundamental cell).

`lift` is the representative in `Ioc (-1/2) (1/2)`, `toV x` the corresponding point of
`EuclideanSpace ℝ (Fin d)`.  We prove that `toV` is measurable, `radius x = ‖toV x‖`,
`toV (-x) = -toV x` almost everywhere, and the integral / integrability / Fourier coefficient
transfer for functions vanishing on `‖v‖ ≥ 1/2`.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped FourierTransform
open scoped BigOperators

namespace LogGas.Torus

/-- The representative of `t ∈ ℝ/ℤ` in `(-1/2, 1/2]`. -/
noncomputable def lift (t : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIoc 1 (-1/2 : ℝ) t : ℝ)

/-- The point of `ℝ^d` with coordinates in `(-1/2, 1/2]` representing `x : 𝕋^d`. -/
noncomputable def toV {d : ℕ} (x : T d) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => lift (x i))

theorem lift_mem (t : AddCircle (1 : ℝ)) : lift t ∈ Ioc (-1/2 : ℝ) (1/2) := by
  have := (AddCircle.equivIoc 1 (-1/2 : ℝ) t).2
  simpa [lift, show (-1/2 : ℝ) + 1 = 1/2 by norm_num] using this

theorem lift_coe (t : AddCircle (1 : ℝ)) : ((lift t : ℝ) : AddCircle (1 : ℝ)) = t :=
  AddCircle.coe_equivIoc

theorem lift_of_mem {y : ℝ} (hy : y ∈ Ioc (-1/2 : ℝ) (1/2)) :
    lift (y : AddCircle (1 : ℝ)) = y := by
  have hy' : y ∈ Ioc (-1/2 : ℝ) (-1/2 + 1) := by
    simpa [show (-1/2 : ℝ) + 1 = 1/2 by norm_num] using hy
  simp only [lift]
  rw [AddCircle.equivIoc_coe_of_mem hy']

theorem measurable_lift : Measurable (lift : AddCircle (1 : ℝ) → ℝ) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 (-1/2 : ℝ)).measurable

theorem measurable_toV {d : ℕ} : Measurable (toV : T d → EuclideanSpace ℝ (Fin d)) := by
  unfold toV
  exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp
    (measurable_pi_iff.mpr fun i => measurable_lift.comp (measurable_pi_apply i))

theorem abs_lift (t : AddCircle (1 : ℝ)) : dist t 0 = |lift t| := by
  have h := lift_mem t
  conv_lhs => rw [← lift_coe t]
  rw [dist_zero_right, (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2]
  rw [abs_one, abs_le]; constructor <;> linarith [h.1, h.2]

theorem radius_eq_norm_toV {d : ℕ} (x : T d) : radius x = ‖toV x‖ := by
  unfold radius
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_lift]
  simp [toV, sq_abs]

theorem toV_neg_ae (d : ℕ) : ∀ᵐ x ∂unif d, toV (-x) = -toV x := by
  -- fails only when some coordinate equals the point `1/2` (the antipode)
  have h1 : ∀ i : Fin d, ∀ᵐ x ∂unif d, x i ≠ ((1/2 : ℝ) : AddCircle (1 : ℝ)) := by
    intro i
    have hm : Measure.map (fun x : T d => x i) (unif d) =
        (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
      unfold unif
      exact (measurePreserving_eval (fun _ => (AddCircle.haarAddCircle :
        Measure (AddCircle (1 : ℝ)))) i).map_eq
    have hs : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))
        {((1/2 : ℝ) : AddCircle (1 : ℝ))} = 0 := by
      have := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
      simp at this
      rw [← this]
      refine measure_mono_null (t := Metric.closedBall ((1/2 : ℝ) : AddCircle (1 : ℝ)) 0)
        (by simp) ?_
      rw [AddCircle.volume_closedBall]; simp
    rw [ae_iff]
    have : {x : T d | ¬ x i ≠ ((1/2 : ℝ) : AddCircle (1 : ℝ))} =
        (fun x : T d => x i) ⁻¹' {((1/2 : ℝ) : AddCircle (1 : ℝ))} := by ext; simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _), hm, hs]
  have h2 := ae_all_iff.mpr h1
  filter_upwards [h2] with x hx
  ext i
  have hxi := hx i
  have hl := lift_mem (x i)
  have hl2 : lift (-x i) = - lift (x i) := by
    have hne : lift (x i) ≠ 1/2 := by
      intro h; apply hxi; rw [← lift_coe (x i), h]
    have hm : -lift (x i) ∈ Ioc (-1/2 : ℝ) (1/2) :=
      ⟨by have := lt_of_le_of_ne hl.2 hne; linarith, by linarith [hl.1]⟩
    have : (-x i) = ((-lift (x i) : ℝ) : AddCircle (1 : ℝ)) := by
      rw [AddCircle.coe_neg, lift_coe]
    rw [this, lift_of_mem hm]
  simp [toV, hl2]

/-- The cube `(-1/2, 1/2]^d`. -/
private def perCube (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (-1/2 : ℝ) (1/2)}

private theorem perCube_eq (d : ℕ) :
    {x : Fin d → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin d => (-1/2 : ℝ)) i)
      ((fun _ : Fin d => (-1/2 : ℝ)) i + 1)} = perCube d := by
  ext x
  simp only [perCube, mem_ofPred_eq, show (-1/2 : ℝ) + 1 = 1/2 by norm_num]

private theorem per_toV_mk {d : ℕ} (y : Fin d → ℝ) (hy : y ∈ perCube d) :
    toV (fun i => (y i : AddCircle (1 : ℝ))) = (WithLp.equiv 2 (Fin d → ℝ)).symm y := by
  ext i
  simp only [toV]
  have := hy i
  simpa using lift_of_mem this

private theorem per_ball_sub {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ < 1/2) :
    (WithLp.equiv 2 (Fin d → ℝ)) v ∈ perCube d := by
  intro i
  have : |v i| ≤ ‖v‖ := by
    simpa using PiLp.norm_apply_le v i
  have := abs_lt.mp (lt_of_le_of_lt this hv)
  exact ⟨by show -1/2 < v i; linarith [this.1], by show v i ≤ 1/2; linarith [this.2]⟩

private theorem per_support {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : EuclideanSpace ℝ (Fin d) → E)
    (hF : ∀ v, (1/2 : ℝ) ≤ ‖v‖ → F v = 0) (y : Fin d → ℝ) (hy : y ∉ perCube d) :
    F ((WithLp.equiv 2 (Fin d → ℝ)).symm y) = 0 := by
  apply hF
  by_contra h
  push Not at h
  apply hy
  simpa using per_ball_sub ((WithLp.equiv 2 (Fin d → ℝ)).symm y) h

section
/-- Same instance as used locally in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
noncomputable local instance perMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

private theorem per_integral_aux {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin d) → E) :
    ∫ x, f x ∂unif d = ∫ y in perCube d, f (fun i => (y i : AddCircle (1 : ℝ))) := by
  have h := UnitAddTorus.integral_preimage f (fun _ : Fin d => (-1/2 : ℝ))
  rw [perCube_eq] at h
  exact h

private theorem per_integrable_aux {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (G : (Fin d → ℝ) → E) (hG : Integrable G) :
    Integrable (fun x : T d => G (fun i => lift (x i))) (unif d) := by
  have e := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (-1/2 : ℝ))
  have hmp := UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin d => (-1/2 : ℝ))
  have h1 : Integrable (fun y : {x : Fin d → ℝ // ∀ i, x i ∈ Ioc ((fun _ : Fin d => (-1/2 : ℝ)) i)
      ((fun _ : Fin d => (-1/2 : ℝ)) i + 1)} => G y.1)
      (Measure.comap Subtype.val volume) := by
    have := (integrableOn_iff_comap_subtypeVal (μ := volume) (f := G)
      (s := {x : Fin d → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin d => (-1/2 : ℝ)) i)
        ((fun _ : Fin d => (-1/2 : ℝ)) i + 1)})
      (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))).1 hG.integrableOn
    exact this
  have := (hmp.integrable_comp_emb
    (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d => (-1/2 : ℝ))).measurableEmbedding).2 h1
  exact this
end

private theorem per_integral {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : EuclideanSpace ℝ (Fin d) → E)
    (hF : ∀ v, (1/2 : ℝ) ≤ ‖v‖ → F v = 0) :
    ∫ x, F (toV x) ∂unif d = ∫ v, F v := by
  have h' := per_integral_aux (fun x : T d => F (toV x))
  refine h'.trans ?_
  have hc : ∀ y ∈ perCube d, F (toV (fun i => (y i : AddCircle (1 : ℝ)))) =
      F ((WithLp.equiv 2 (Fin d → ℝ)).symm y) := fun y hy => by rw [per_toV_mk y hy]
  have hm : MeasurableSet (perCube d) := by
    rw [← perCube_eq]; exact MeasurableSet.univ_pi' (fun i => measurableSet_Ioc)
  rw [setIntegral_congr_fun hm hc,
    setIntegral_eq_integral_of_forall_compl_eq_zero (per_support F hF)]
  exact (MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d))).integral_comp' F

theorem integral_comp_toV {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (hF : ∀ v, (1/2 : ℝ) ≤ ‖v‖ → F v = 0) (_hFi : Integrable F) :
    ∫ x, F (toV x) ∂unif d = ∫ v, F v :=
  per_integral F hF

theorem integrable_comp_toV {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (_hF : ∀ v, (1/2 : ℝ) ≤ ‖v‖ → F v = 0) (hFi : Integrable F) :
    Integrable (fun x => F (toV x)) (unif d) := by
  have hmp := MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d))
  have hG : Integrable (fun y : Fin d → ℝ => F ((WithLp.equiv 2 (Fin d → ℝ)).symm y)) := by
    have := (hmp.integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.symm.measurableEmbedding).2 hFi
    exact this
  exact per_integrable_aux _ hG

private theorem per_negChar {d : ℕ} (k : Fin d → ℤ) (x : T d) :
    LogGas.Fourier.negChar k x = Complex.exp (((-2 * Real.pi *
      inner ℝ (toV x) ((WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (k i : ℝ))) : ℝ) : ℂ) *
        Complex.I) := by
  unfold LogGas.Fourier.negChar
  have : ∀ i, fourier (-(k i)) (x i) = Complex.exp (((-2 * Real.pi * (k i * lift (x i)) : ℝ) : ℂ)
      * Complex.I) := by
    intro i
    conv_lhs => rw [← lift_coe (x i)]
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  simp_rw [this, ← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  simp [PiLp.inner_apply, toV, Finset.mul_sum, mul_comm]

theorem coeff_comp_toV {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ v, (1/2 : ℝ) ≤ ‖v‖ → F v = 0) (_hFi : Integrable F) (k : Fin d → ℤ) :
    LogGas.Fourier.coeff (fun x => F (toV x)) k =
      𝓕 (fun v => (F v : ℂ)) ((WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (k i : ℝ))) := by
  set ξ : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (k i : ℝ))
  rw [Real.fourier_eq']
  unfold LogGas.Fourier.coeff
  have h := per_integral (fun v : EuclideanSpace ℝ (Fin d) =>
    Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I) • (F v : ℂ))
    (fun v hv => by simp [hF v hv])
  simp_rw [per_negChar] 
  rw [← h]
  simp only [smul_eq_mul]
  rfl

end LogGas.Torus

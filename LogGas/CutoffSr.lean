import LogGas.CutoffFourier

/-!
# Section 2 — the singular cutoff `s_r`

Source: `notes/sec2-cutoff.tex` (2.1), `eq:compact-positive-log-split`; audit E2.

`s_r(v) = φ(0)⁻¹ ∫_0^r φ(v/t) dt/t` on `ℝ^d`.  We prove: `s_r ≥ 0`, `s_r = 0` for `‖v‖ ≥ r/2`,
`s_r(v) ≤ log₊(r/‖v‖)`, measurability, evenness, integrability,
`∫ s_r = r^d/(d φ(0)) ∫ φ`, and `𝓕 s_r (ξ) = φ(0)⁻¹ ∫_0^r t^{d-1} φ̂(tξ) dt`.
-/

open MeasureTheory FourierTransform

namespace LogGas.Cutoff

variable {d : ℕ}

/-- The singular cutoff `s_r`. -/
noncomputable def sR (d : ℕ) (r : ℝ) (v : V d) : ℝ :=
  (phi d 0)⁻¹ * ∫ t in Set.Ioc 0 r, phi d (t⁻¹ • v) / t

/-- The two-variable integrand. -/
private noncomputable def srF (d : ℕ) (t : ℝ) (v : V d) : ℝ := phi d (t⁻¹ • v) / t

private lemma srF_nonneg {t : ℝ} (ht : 0 < t) (v : V d) : 0 ≤ srF d t v :=
  div_nonneg (phi_nonneg _) ht.le

private lemma srF_meas : Measurable (fun p : ℝ × V d => srF d p.1 p.2) :=
  (phi_continuous.measurable.comp (measurable_fst.inv.smul measurable_snd)).div measurable_fst

private lemma srF_integral (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    ∫ v : V d, srF d t v = t ^ (d - 1) * ∫ v, phi d v := by
  unfold srF
  rw [integral_div, Measure.integral_comp_inv_smul_of_nonneg volume (phi d) ht.le,
    finrank_euclideanSpace_fin, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  field_simp
  ring

theorem sR_nonneg (v : V d) (r : ℝ) : 0 ≤ sR d r v := by
  unfold sR
  refine mul_nonneg (inv_nonneg.2 (phi_zero_pos).le) ?_
  exact setIntegral_nonneg measurableSet_Ioc fun t ht => srF_nonneg ht.1 v

theorem sR_support {r : ℝ} (v : V d) (hv : r / 2 ≤ ‖v‖) : sR d r v = 0 := by
  unfold sR
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ))]
  · simp
  · intro t ht
    simp only
    rw [phi_support _, zero_div]
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.1.le, ← div_eq_inv_mul, le_div_iff₀ ht.1]
    nlinarith [ht.2, ht.1]

theorem sR_even (v : V d) (r : ℝ) : sR d r (-v) = sR d r v := by
  unfold sR
  congr 2
  funext t
  rw [smul_neg, phi_even]

theorem measurable_sR (r : ℝ) : Measurable (sR d r) := by
  unfold sR
  refine Measurable.const_mul ?_ _
  exact (srF_meas (d := d)).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Set.Ioc (0 : ℝ) r)) |>.measurable

theorem sR_le_log {r : ℝ} (hr : 0 < r) (v : V d) (hv : v ≠ 0) :
    sR d r v ≤ max 0 (Real.log (r / ‖v‖)) := by
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  by_cases har : r ≤ 2 * ‖v‖
  · rw [sR_support v (by linarith)]
    exact le_max_left _ _
  rw [not_le] at har
  refine le_trans ?_ (le_max_right _ _)
  set a : ℝ := 2 * ‖v‖ with ha
  have ha0 : 0 < a := by positivity
  have hp0 := phi_zero_pos (d := d)
  have hle : ∫ t in Set.Ioc 0 r, phi d (t⁻¹ • v) / t ≤
      ∫ t in Set.Ioc 0 r, (Set.Ioc a r).indicator (fun t => phi d 0 * t⁻¹) t := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun t ht => srF_nonneg ht.1 v)
    · rw [integrable_indicator_iff measurableSet_Ioc]
      have h1 : IntegrableOn (fun t : ℝ => phi d 0 * t⁻¹) (Set.Ioc a r) volume :=
        (continuousOn_const.mul (continuousOn_inv₀.mono
          (fun t (ht : t ∈ Set.Icc a r) => (lt_of_lt_of_le ha0 ht.1).ne'))).integrableOn_Icc.mono_set
          Set.Ioc_subset_Icc_self
      unfold IntegrableOn at h1 ⊢
      rw [Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_left.2 (Set.Ioc_subset_Ioc_left ha0.le)]
      exact h1
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
      beta_reduce
      by_cases hta : t ∈ Set.Ioc a r
      · rw [Set.indicator_of_mem hta, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (phi_le_phi_zero _) (inv_nonneg.2 ht.1.le)
      · rw [Set.indicator_of_notMem hta]
        have : t ≤ a := by
          by_contra h
          exact hta ⟨not_le.1 h, ht.2⟩
        rw [phi_support _, zero_div]
        rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.1.le, ← div_eq_inv_mul, le_div_iff₀ ht.1]
        linarith
  have hint : ∫ t in Set.Ioc 0 r, (Set.Ioc a r).indicator (fun t => phi d 0 * t⁻¹) t
      = phi d 0 * Real.log (r / a) := by
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc_left ha0.le), integral_const_mul,
      ← intervalIntegral.integral_of_le har.le, integral_inv_of_pos ha0 hr]
  unfold sR
  calc (phi d 0)⁻¹ * ∫ t in Set.Ioc 0 r, phi d (t⁻¹ • v) / t
      ≤ (phi d 0)⁻¹ * (phi d 0 * Real.log (r / a)) :=
        mul_le_mul_of_nonneg_left (hle.trans hint.le) (inv_nonneg.2 hp0.le)
    _ = Real.log (r / a) := by field_simp
    _ ≤ Real.log (r / ‖v‖) := by
        apply Real.log_le_log (div_pos hr ha0)
        exact div_le_div_of_nonneg_left hr.le hn (by linarith)

private lemma srF_integrable_slice {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : V d => srF d t v) := by
  unfold srF
  exact ((integrable_comp_smul_iff volume (phi d) (inv_ne_zero ht.ne')).2 phi_integrable).div_const _

private lemma srF_integrable {r : ℝ} (hd : 1 ≤ d) :
    Integrable (fun p : ℝ × V d => srF d p.1 p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) r)).prod (volume : Measure (V d))) := by
  rw [integrable_prod_iff srF_meas.aestronglyMeasurable]
  refine ⟨(ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall fun t ht => srF_integrable_slice ht.1), ?_⟩
  have h1 : Integrable (fun t : ℝ => t ^ (d - 1) * ∫ v, phi d v)
      (volume.restrict (Set.Ioc (0 : ℝ) r)) :=
    (((continuous_id.pow (d - 1)).mul continuous_const).integrableOn_Ioc)
  refine h1.congr ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_))
  simp only
  rw [← srF_integral hd ht.1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => by
    simp [Real.norm_of_nonneg (srF_nonneg ht.1 v)]) |>.symm

theorem integrable_sR (hd : 1 ≤ d) (r : ℝ) : Integrable (sR d r) :=
  ((srF_integrable (r := r) hd).integral_prod_right).const_mul _

theorem integral_sR (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    ∫ v, sR d r v = r ^ d / (d * phi d 0) * ∫ v, phi d v := by
  have hsw := integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) r))
    (ν := (volume : Measure (V d))) (f := srF d) (srF_integrable hd)
  simp only [srF] at hsw
  unfold sR
  rw [integral_const_mul, ← hsw]
  have h2 : ∫ t in Set.Ioc 0 r, ∫ v : V d, srF d t v = ∫ t in Set.Ioc 0 r, t ^ (d - 1) * ∫ v, phi d v :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => srF_integral hd ht.1
  have h3 : ∫ t in Set.Ioc 0 r, t ^ (d - 1) = r ^ d / d := by
    rw [← intervalIntegral.integral_of_le hr.le, integral_pow]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp
  have := phi_zero_pos (d := d)
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  simp only [srF] at h2 ⊢
  rw [h2, integral_mul_const, h3]
  field_simp

private lemma srF_fourier_slice (hd : 1 ≤ d) (ξ : V d) {t : ℝ} (ht : 0 < t) :
    ∫ v : V d, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) * (srF d t v : ℂ) =
      ((t ^ (d - 1) * phiHat d (t • ξ) : ℝ) : ℂ) := by
  set f : V d → ℂ := fun w =>
    Complex.exp (↑(-2 * Real.pi * inner ℝ w (t • ξ)) * Complex.I) * (phi d w : ℂ) with hf
  have h1 : ∀ v : V d, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) * (srF d t v : ℂ)
      = (t⁻¹ : ℝ) • f (t⁻¹ • v) := by
    intro v
    simp only [hf, srF, inner_smul_left, inner_smul_right, Complex.real_smul]
    have : t * ((starRingEnd ℝ) t⁻¹ * inner ℝ v ξ) = inner ℝ v ξ := by
      simp only [conj_trivial]; field_simp
    rw [this]
    push_cast
    ring
  have h2 : ∫ w : V d, f w = (phiHat d (t • ξ) : ℂ) := by
    rw [← fourier_phi_eq (t • ξ), Real.fourier_eq']
    simp only [hf, smul_eq_mul]
  simp only [h1]
  rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume f ht.le,
    finrank_euclideanSpace_fin, h2]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp only [Complex.real_smul]
  push_cast
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring

theorem fourier_sR (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (ξ : V d) :
    𝓕 (fun v => (sR d r v : ℂ)) ξ =
      (((phi d 0)⁻¹ * ∫ t in Set.Ioc 0 r, t ^ (d - 1) * phiHat d (t • ξ) : ℝ) : ℂ) := by
  set H : ℝ → V d → ℂ := fun t v =>
    Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) * (srF d t v : ℂ) with hH
  have hmeas : Measurable (fun p : ℝ × V d => H p.1 p.2) := by
    have hi : Measurable (fun p : ℝ × V d => (inner ℝ p.2 ξ : ℝ)) :=
      (continuous_snd.inner continuous_const).measurable
    exact (Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp
      ((measurable_const.mul hi))).mul_const Complex.I))).mul
      (Complex.measurable_ofReal.comp srF_meas)
  have hI : Integrable (Function.uncurry H)
      ((volume.restrict (Set.Ioc (0 : ℝ) r)).prod (volume : Measure (V d))) := by
    refine (srF_integrable (r := r) hd).mono hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hH, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real]
    exact le_refl _
  have hsw := integral_integral_swap hI
  have hA : ∀ v : V d, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (sR d r v : ℂ)
      = ((phi d 0)⁻¹ : ℝ) * ∫ t in Set.Ioc 0 r, H t v := by
    intro v
    simp only [hH, sR, smul_eq_mul]
    rw [integral_const_mul, Complex.ofReal_mul, integral_complex_ofReal]
    simp only [srF]
    push_cast
    ring
  have hB : ∫ t in Set.Ioc (0 : ℝ) r, ∫ v : V d, H t v
      = ((∫ t in Set.Ioc 0 r, t ^ (d - 1) * phiHat d (t • ξ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => srF_fourier_slice hd ξ ht.1
  rw [Real.fourier_eq']
  simp only [hA]
  rw [integral_const_mul, ← hsw, hB]
  push_cast
  rfl

end LogGas.Cutoff

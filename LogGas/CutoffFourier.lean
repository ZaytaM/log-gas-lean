import LogGas.CutoffProfile

/-!
# Section 2 — Fourier transform of the cutoff profile `φ = χ * χ`

Source: `notes/sec2-cutoff.tex` (2.2), `eq:compact-split-fourier-order`; audit E2.

Convention: `𝓕 f ξ = ∫ e^{-2π i ⟪x, ξ⟫} f x dx` (Mathlib's `Real.fourierIntegral`) on `ℝ^d`.
`phiHat d ξ` is the real part of `𝓕 φ ξ`; we prove `𝓕 φ ξ = phiHat d ξ` (`φ̂` is real, since
`φ̂ = (χ̂)²` and `χ̂` is real because `χ` is real and even), `φ̂ ≥ 0`, `φ̂` radial, continuous,
integrable, with decay `|φ̂ ξ| ≤ C (1+‖ξ‖)^{-(d+2)}`, and `∫ φ̂ = φ 0` (Fourier inversion at `0`).
-/

open MeasureTheory Convolution FourierTransform Submodule

namespace LogGas.Cutoff

variable {d : ℕ}

/-- The Fourier transform of `φ`, as a real function. -/
noncomputable def phiHat (d : ℕ) (ξ : V d) : ℝ := (𝓕 (fun x => (phi d x : ℂ)) ξ).re

private lemma cf_chiC_integrable : Integrable (fun x : V d => (chi d x : ℂ)) :=
  (Complex.continuous_ofReal.comp chi_continuous).integrable_of_hasCompactSupport
    (chi_hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) (by simp))

/-- `χ̂` is real. -/
private lemma cf_fourier_chi_real (ξ : V d) :
    𝓕 (fun x => (chi d x : ℂ)) ξ = ((∫ x, Real.cos (2 * Real.pi * inner ℝ x ξ) * chi d x : ℝ) : ℂ) := by
  have hint := cf_chiC_integrable (d := d)
  set g : V d → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I) • (chi d x : ℂ)
    with hg
  have hF : 𝓕 (fun x => (chi d x : ℂ)) ξ = ∫ x, g x := by
    rw [Real.fourier_eq']
  have hgi : Integrable g := by
    have := Real.fourierIntegral_convergent_iff ξ |>.2 hint
    simpa [hg, Circle.smul_def, Real.fourierChar_apply] using this
  have hneg : ∫ x, g x = ∫ x, g (-x) := (integral_neg_eq_self g volume).symm
  have hgn : Integrable (fun x => g (-x)) := hgi.comp_neg
  have h2 : (2 : ℂ) * ∫ x, g x = ∫ x, (g x + g (-x)) := by
    rw [integral_add hgi hgn, ← hneg]; ring
  have hsum : ∀ x, g x + g (-x) = ((2 * (Real.cos (2 * Real.pi * inner ℝ x ξ) * chi d x) : ℝ) : ℂ) := by
    intro x
    have key : ∀ t : ℂ, Complex.exp (-(t * Complex.I)) + Complex.exp (t * Complex.I) = 2 * Complex.cos t := by
      intro t; rw [Complex.cos, neg_mul]; ring
    simp only [hg, smul_eq_mul, chi_even, inner_neg_left]
    have := key (2 * Real.pi * (inner ℝ x ξ : ℝ))
    have e1 : (↑(-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I
        = -(2 * Real.pi * (inner ℝ x ξ : ℝ) * Complex.I) := by push_cast; ring
    have e2 : (↑(-2 * Real.pi * -inner ℝ x ξ : ℝ) : ℂ) * Complex.I
        = 2 * Real.pi * (inner ℝ x ξ : ℝ) * Complex.I := by push_cast; ring
    rw [e1, e2]
    push_cast at this ⊢
    linear_combination (chi d x : ℂ) * this
  rw [hF]
  have h3 : ∫ x, (g x + g (-x)) = ((∫ x, 2 * (Real.cos (2 * Real.pi * inner ℝ x ξ) * chi d x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; exact integral_congr_ae (Filter.Eventually.of_forall hsum)
  rw [integral_const_mul] at h3
  have : ∫ x, g x = ((∫ x, Real.cos (2 * Real.pi * inner ℝ x ξ) * chi d x : ℝ) : ℂ) := by
    have h4 := h2.trans h3
    push_cast at h4
    linear_combination h4 / 2
  exact this

private lemma cf_phiC_eq_conv :
    (fun x : V d => (phi d x : ℂ)) =
      (fun x : V d => (chi d x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun x : V d => (chi d x : ℂ)) := by
  funext x
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  unfold phi
  rw [← integral_complex_ofReal]
  push_cast
  rfl

/-- `φ̂ = (χ̂)²`, with `χ̂` real. -/
private lemma cf_fourier_phi (ξ : V d) :
    𝓕 (fun x => (phi d x : ℂ)) ξ =
      (((∫ x, Real.cos (2 * Real.pi * inner ℝ x ξ) * chi d x) ^ 2 : ℝ) : ℂ) := by
  rw [cf_phiC_eq_conv, Real.fourier_mul_convolution_eq cf_chiC_integrable cf_chiC_integrable,
    cf_fourier_chi_real]
  push_cast; ring

theorem fourier_phi_eq (ξ : V d) :
    𝓕 (fun x => (phi d x : ℂ)) ξ = (phiHat d ξ : ℂ) := by
  rw [cf_fourier_phi]
  unfold phiHat
  rw [cf_fourier_phi, Complex.ofReal_re]

theorem phiHat_nonneg (ξ : V d) : 0 ≤ phiHat d ξ := by
  rw [phiHat, cf_fourier_phi, Complex.ofReal_re]; positivity

theorem phiHat_radial (ξ η : V d) (h : ‖ξ‖ = ‖η‖) : phiHat d ξ = phiHat d η := by
  obtain ⟨R, hR⟩ : ∃ R : V d ≃ₗᵢ[ℝ] V d, R ξ = η :=
    ⟨reflection (ℝ ∙ (ξ - η))ᗮ, reflection_sub h⟩
  subst hR
  have := Real.fourier_comp_linearIsometry R (fun x : V d => (phi d x : ℂ)) ξ
  have e : ((fun x : V d => (phi d x : ℂ)) ∘ R) = fun x => (phi d x : ℂ) := by
    funext x; simp [phi_radial (R x) x (by simp)]
  rw [e] at this
  unfold phiHat
  rw [this]

/-- `φ` as a (complex valued) Schwartz function. -/
private noncomputable def cfPhiS (d : ℕ) : SchwartzMap (V d) ℂ :=
  (phi_hasCompactSupport (d := d)).comp_left (g := ((↑) : ℝ → ℂ)) (by simp) |>.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp phi_contDiff)

private lemma cf_fourier_cfPhiS (ξ : V d) :
    𝓕 (cfPhiS d) ξ = 𝓕 (fun x => (phi d x : ℂ)) ξ := rfl

private lemma cf_phiHat_eq (ξ : V d) : phiHat d ξ = (𝓕 (cfPhiS d) ξ).re := rfl

theorem phiHat_continuous : Continuous (phiHat d) := by
  have : phiHat d = fun ξ => (𝓕 (cfPhiS d) ξ).re := funext cf_phiHat_eq
  rw [this]
  exact Complex.continuous_re.comp (𝓕 (cfPhiS d)).continuous

theorem phiHat_integrable : Integrable (phiHat d) := by
  have : phiHat d = fun ξ => (𝓕 (cfPhiS d) ξ).re := funext cf_phiHat_eq
  rw [this]
  exact (𝓕 (cfPhiS d)).integrable.re

theorem phiHat_decay : ∃ C, ∀ ξ : V d, |phiHat d ξ| ≤ C * (1 + ‖ξ‖) ^ (-((d : ℝ) + 2)) := by
  set F := 𝓕 (cfPhiS d) with hF
  set C : ℝ := 2 ^ (d + 2) * (Finset.Iic (d + 2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨C, fun ξ => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 2, 0)) (k := d + 2)
    (n := 0) le_rfl le_rfl F ξ
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖ξ‖) := by positivity
  have hre : |phiHat d ξ| ≤ ‖F ξ‖ := by
    rw [cf_phiHat_eq]; exact Complex.abs_re_le_norm _
  have hpow : (1 + ‖ξ‖) ^ (-((d : ℝ) + 2)) = ((1 + ‖ξ‖) ^ (d + 2))⁻¹ := by
    rw [Real.rpow_neg hpos.le, show ((d : ℝ) + 2) = ((d + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hpow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc |phiHat d ξ| * (1 + ‖ξ‖) ^ (d + 2) ≤ ‖F ξ‖ * (1 + ‖ξ‖) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right hre (by positivity)
    _ = (1 + ‖ξ‖) ^ (d + 2) * ‖F ξ‖ := by ring
    _ ≤ C := h

theorem integral_phiHat : ∫ ξ, phiHat d ξ = phi d 0 := by
  have h1 := (cfPhiS d).continuous.fourierInv_fourier_eq (cfPhiS d).integrable
    (𝓕 (cfPhiS d)).integrable
  have h2 := congrFun h1 0
  rw [Real.fourierInv_eq'] at h2
  have h3 : ∀ v : V d, (𝓕 (⇑(cfPhiS d)) v) = (phiHat d v : ℂ) := fun v => fourier_phi_eq v
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    h3] at h2
  rw [integral_complex_ofReal] at h2
  have h6 : (cfPhiS d) 0 = (phi d 0 : ℂ) := rfl
  rw [h6] at h2
  exact_mod_cast h2

end LogGas.Cutoff

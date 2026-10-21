import Mathlib

/-!
# Section 2 — the cutoff profile `χ` and `φ = χ * χ`

Source: `notes/sec2-cutoff.tex` (2.1), `eq:compact-positive-log-split`; audit E2.

`χ` is the smooth radial bump `x ↦ smoothTransition (1 - 16 ‖x‖²)` on `ℝ^d` (Euclidean norm),
nonnegative, `χ 0 = 1`, supported in the closed ball of radius `1/4`.  (Mathlib's generic
`ContDiffBump` is not provably radial, hence the explicit definition.)
`φ x = ∫ χ(y) χ(x - y) dy` is the convolution `χ * χ`; it is smooth, radial, even, bounded by
`φ 0`, and supported in the closed ball of radius `1/2`.
-/

open MeasureTheory Convolution Submodule

namespace LogGas.Cutoff

/-- Euclidean space `ℝ^d`. -/
abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Smooth radial bump, `χ 0 = 1`, supported in `‖x‖ < 1/4`. -/
noncomputable def chi (d : ℕ) : V d → ℝ :=
  fun x => Real.smoothTransition (1 - 16 * ‖x‖ ^ 2)

/-- `φ = χ * χ`. -/
noncomputable def phi (d : ℕ) (x : V d) : ℝ := ∫ y, chi d y * chi d (x - y)

variable {d : ℕ}

theorem chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) (chi d) := by
  unfold chi
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem chi_nonneg (x : V d) : 0 ≤ chi d x := Real.smoothTransition.nonneg _

theorem chi_support (x : V d) (hx : 1 / 4 ≤ ‖x‖) : chi d x = 0 := by
  unfold chi
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]

theorem chi_radial (x y : V d) (h : ‖x‖ = ‖y‖) : chi d x = chi d y := by
  simp [chi, h]

theorem chi_zero_pos : 0 < chi d 0 := by
  simp [chi]

theorem chi_hasCompactSupport : HasCompactSupport (chi d) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V d) (1 / 4))
  intro x hx
  apply chi_support
  have : ¬ ‖x‖ ≤ 1 / 4 := by simpa using hx
  exact (not_le.mp this).le

theorem chi_even (x : V d) : chi d (-x) = chi d x := chi_radial _ _ (by simp)

theorem chi_continuous : Continuous (chi d) := chi_contDiff.continuous

theorem phi_eq_convolution (x : V d) :
    phi d x = (chi d ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] chi d) x := by
  rw [convolution_def]; rfl

theorem phi_contDiff : ContDiff ℝ (⊤ : ℕ∞) (phi d) := by
  have : phi d = (chi d ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] chi d) :=
    funext phi_eq_convolution
  rw [this]
  exact chi_hasCompactSupport.contDiff_convolution_left _ chi_contDiff
    (chi_continuous.locallyIntegrable)

theorem phi_continuous : Continuous (phi d) := phi_contDiff.continuous

theorem phi_nonneg (x : V d) : 0 ≤ phi d x :=
  integral_nonneg fun y => mul_nonneg (chi_nonneg _) (chi_nonneg _)

theorem phi_support (x : V d) (hx : 1 / 2 ≤ ‖x‖) : phi d x = 0 := by
  unfold phi
  have : ∀ y, chi d y * chi d (x - y) = 0 := by
    intro y
    by_contra hne
    have h1 : chi d y ≠ 0 := left_ne_zero_of_mul hne
    have h2 : chi d (x - y) ≠ 0 := right_ne_zero_of_mul hne
    have a : ‖y‖ < 1 / 4 := by by_contra h; exact h1 (chi_support _ (not_lt.mp h))
    have b : ‖x - y‖ < 1 / 4 := by by_contra h; exact h2 (chi_support _ (not_lt.mp h))
    have := norm_le_norm_add_norm_sub' x y
    have := norm_sub_le x y
    have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x - y) + y‖ := by simp
        _ ≤ _ := norm_add_le _ _
    linarith
  simp [this]

theorem phi_hasCompactSupport : HasCompactSupport (phi d) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V d) (1 / 2))
  intro x hx
  apply phi_support
  have : ¬ ‖x‖ ≤ 1 / 2 := by simpa using hx
  exact (not_le.mp this).le

theorem phi_integrable : Integrable (phi d) :=
  phi_continuous.integrable_of_hasCompactSupport phi_hasCompactSupport

theorem phi_even (x : V d) : phi d (-x) = phi d x := by
  unfold phi
  rw [← integral_neg_eq_self (fun y => chi d y * chi d (-x - y)) volume]
  congr 1
  funext y
  have : ‖-x - -y‖ = ‖x - y‖ := by
    rw [show -x - -y = -(x - y) by abel, norm_neg]
  rw [chi_even, chi_radial _ _ this]

theorem phi_zero_eq (d : ℕ) : phi d 0 = ∫ y, chi d y ^ 2 := by
  unfold phi
  congr 1
  funext y
  rw [zero_sub, chi_even, sq]

theorem chi_sq_hcs : HasCompactSupport (fun y : V d => chi d y ^ 2) :=
  chi_hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)

theorem phi_zero_pos : 0 < phi d 0 := by
  rw [phi_zero_eq]
  exact (chi_continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 0) (chi_sq_hcs)
    (fun x => by simp [sq_nonneg]) (by simpa using chi_zero_pos.ne')

theorem phi_le_phi_zero (x : V d) : phi d x ≤ phi d 0 := by
  have hi : Integrable (fun y => chi d y ^ 2) :=
    (chi_continuous.pow 2).integrable_of_hasCompactSupport
      chi_sq_hcs
  have hi2 : Integrable (fun y => chi d (x - y) ^ 2) := by
    have := hi.comp_sub_left x
    exact this
  have hint : Integrable (fun y => chi d y * chi d (x - y)) :=
    ((chi_continuous.mul (chi_continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (chi_hasCompactSupport.mul_right))
  have h1 : phi d x ≤ ∫ y, (chi d y ^ 2 + chi d (x - y) ^ 2) / 2 := by
    unfold phi
    refine integral_mono hint ((hi.add hi2).div_const 2) fun y => ?_
    nlinarith [sq_nonneg (chi d y - chi d (x - y))]
  have h2 : ∫ y, (chi d y ^ 2 + chi d (x - y) ^ 2) / 2 = phi d 0 := by
    rw [integral_div, integral_add hi hi2, integral_sub_left_eq_self (fun y => chi d y ^ 2) volume x,
      phi_zero_eq]
    ring
  linarith

theorem phi_radial (x y : V d) (h : ‖x‖ = ‖y‖) : phi d x = phi d y := by
  obtain ⟨R, hR⟩ : ∃ R : V d ≃ₗᵢ[ℝ] V d, R x = y :=
    ⟨reflection (ℝ ∙ (x - y))ᗮ, reflection_sub h⟩
  subst hR
  have hmp : MeasurePreserving R volume volume := R.measurePreserving
  have key := hmp.integral_comp R.toHomeomorph.measurableEmbedding
    (fun w => chi d w * chi d (R x - w))
  unfold phi
  rw [← key]
  congr 1
  funext z
  have e1 : chi d (R z) = chi d z := chi_radial _ _ (by simp)
  have e2 : chi d (R x - R z) = chi d (x - z) := chi_radial _ _ (by rw [← map_sub, LinearIsometryEquiv.norm_map])
  show chi d z * chi d (x - z) = chi d (R z) * chi d (R x - R z)
  rw [e1, e2]

end LogGas.Cutoff

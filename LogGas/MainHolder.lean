import Mathlib

/-!
# Hölder split of the good-event partition

Source: `notes/sec2-cutoff.tex`, eq. `eq:physical-cutoff-holder` (audit D1).
* `holder_split`: `∫ 1_A e^{F+G} ≤ (∫ e^{pF})^{1/p} (∫ 1_A e^{qG})^{1/q}` for Hölder conjugate `p, q`;
* `lintegral_split_compl`: `∫ e^H = ∫ 1_A e^H + ∫ 1_{Aᶜ} e^H`.
-/

set_option autoImplicit false

open MeasureTheory

namespace LogGas.Main

variable {Ω : Type*} [MeasurableSpace Ω]

theorem holder_split (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (p q : ℝ) (hpq : p.HolderConjugate q) :
    ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (F ω + G ω))) ω ∂μ
      ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (p * F ω)) ∂μ) ^ (1 / p)
        * (∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (q * G ω))) ω ∂μ) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (F ω)) with hf
  set g : Ω → ENNReal := fun ω => A.indicator (fun ω => ENNReal.ofReal (Real.exp (G ω))) ω with hg
  have hfm : AEMeasurable f μ :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hF)).aemeasurable
  have hgm : AEMeasurable g μ :=
    (Measurable.indicator (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hG)) hA).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hfm hgm
  have e1 : ∀ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (F ω + G ω))) ω = (f * g) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg, hf, Set.indicator_of_mem hω, Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    · simp [hg, hω]
  have e2 : ∀ ω, (f ω) ^ p = ENNReal.ofReal (Real.exp (p * F ω)) := by
    intro ω
    simp only [hf]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp0.le, ← Real.exp_mul, mul_comm]
  have e3 : ∀ ω, (g ω) ^ q = A.indicator (fun ω => ENNReal.ofReal (Real.exp (q * G ω))) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg, Set.indicator_of_mem hω]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul, mul_comm]
    · simp [hg, hω, ENNReal.zero_rpow_of_pos hq0]
  simp only [e1, e2, e3] at *
  exact h

theorem lintegral_split_compl (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (H : Ω → ℝ)
    (hH : Measurable H) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (H ω)) ∂μ
      = ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (H ω))) ω ∂μ
        + ∫⁻ ω, Aᶜ.indicator (fun ω => ENNReal.ofReal (Real.exp (H ω))) ω ∂μ := by
  rw [lintegral_indicator hA, lintegral_indicator hA.compl]
  exact (lintegral_add_compl _ hA).symm

end LogGas.Main

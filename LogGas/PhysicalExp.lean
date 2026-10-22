import LogGas.TorusBase
import LogGas.ExpIntegrable

/-!
# Physical slice exponential bound

Source: `notes/sec3-badevent.tex` (`A_b < ∞` for `b < 2d`), `notes/sec5-singular.tex` (5.8),
audit C6/E5.  If `g = b + (s - c)` a.e. with `b` continuous and `s ≤ max 0 log (r / radius)`,
then `y ↦ exp ((b'/2) g (x - y))` is integrable for `0 < b' < 2d`, with an integral bound
`A` uniform in `x` (translation/reflection invariance of `unif d`).
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus

namespace LogGas.Physical

private lemma physexp_log_le {d : ℕ} (r : ℝ) (hr : 0 < r) (z : T d) :
    max 0 (Real.log (r / radius z)) ≤ max 0 (Real.log (r / dist z 0)) := by
  have hrad0 : 0 ≤ radius z := (dist_nonneg).trans (dist_zero_le_radius z)
  rcases hrad0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hd := radius_le_sqrt_mul z
    have hdz := dist_zero_le_radius z
    rcases (dist_nonneg (x := z) (y := 0)).eq_or_lt with h1 | h1
    · rw [← h1] at hd; simp at hd; linarith
    · refine max_le_max le_rfl (Real.log_le_log (by positivity) ?_)
      exact div_le_div_of_nonneg_left hr.le h1 hdz

theorem exp_slice_bound {d : ℕ} (hd : 1 ≤ d) (g b s : T d → ℝ) (hg : Measurable g)
    (hb : Continuous b) (c r : ℝ) (hr : 0 < r)
    (hgs : ∀ᵐ x ∂unif d, g x = b x + (s x - c))
    (hsle : ∀ᵐ x ∂unif d, s x ≤ max 0 (Real.log (r / radius x)))
    (b' : ℝ) (hb0 : 0 < b') (hb' : b' < 2 * d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : T d,
      Integrable (fun y => Real.exp ((b' / 2) * g (x - y))) (unif d) ∧
      ∫ y, Real.exp ((b' / 2) * g (x - y)) ∂unif d ≤ A := by
  obtain ⟨Cb, hCb⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuousOn
  set α : ℝ := b' / 2 with hα
  have hα0 : 0 ≤ α := by positivity
  have hαd : α < d := by rw [hα]; linarith
  have hF := integrable_exp_log_sing (unif d) d ((2:ℝ) ^ d) r α hr hα0 hαd
    (fun ρ hρ => ball_vol d ρ hρ)
  set M : ℝ := Real.exp (α * (Cb + |c|)) with hM
  have hGint : Integrable (fun z => Real.exp (α * g z)) (unif d) := by
    refine (hF.const_mul M).mono' ?_ ?_
    · exact (Real.measurable_exp.comp (hg.const_mul α)).aestronglyMeasurable
    · filter_upwards [hgs, hsle] with z h1 h2
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hM, ← Real.exp_add, ← mul_add]
      apply Real.exp_le_exp.2
      refine mul_le_mul_of_nonneg_left ?_ hα0
      have hbz := hCb z (Set.mem_univ z)
      rw [Real.norm_eq_abs] at hbz
      have := physexp_log_le (d := d) r hr z
      have := neg_abs_le c
      have := le_abs_self (b z)
      have := le_abs_self c
      rw [h1]; linarith
  refine ⟨max 1 (∫ z, Real.exp (α * g z) ∂unif d), le_max_left _ _, fun x => ⟨?_, ?_⟩⟩
  · exact ((unif d).measurePreserving_sub_left x).integrable_comp_of_integrable hGint
  · rw [integral_sub_left_eq_self (fun z => Real.exp (α * g z)) (unif d) x]
    exact le_max_right _ _

end LogGas.Physical

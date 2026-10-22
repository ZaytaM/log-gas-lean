import LogGas.BulkHist
import LogGas.BulkTorus
import LogGas.MainBad
import LogGas.PhysicalExp

/-!
# Contract milestone theorems A4, A6, PEXP, M3

Sources: `notes/appendixA.tex` eqs. (A.6), (A.9); `notes/sec3-badevent.tex`
eq. `eq:physical-bad-probability`; audit E5, E6, E9.

* `LogGas.Bulk.ell_hist` — A4: `⟨f_L, T μ_N⟩ = c · ℓ` for the histogram;
* `LogGas.Bulk.rJ_bound` — A6: the remainder `r_J` is uniformly small on the torus grid;
* `LogGas.Physical.log_exp_integrable` — PEXP: `exp (α max(0, log (r/|z|)))` is integrable on the
  Euclidean torus for `α < d`;
* `LogGas.Main.parameter_choice` — M3: the bad-event term is bounded independently of `N`, `β`.

No deviations from the stated interfaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

section
variable {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE]
  {M N : ℕ} {Ω : Type*} {K : E → E → ℝ}

/-- Eq. (A.6) for the histogram: `⟨f_L, T μ_N⟩ = c · ℓ` with `c` the histogram coefficients. -/
theorem ell_hist (hK : Measurable (Function.uncurry K)) (CK : ℝ) (hKb : ∀ x y, |K x y| ≤ CK)
    (bx : Boxes μE M) (X : Fin N → Ω → E) (ω : Ω) :
    empPair μE K (hist X bx ω) X ω = histCoef X bx ω ⬝ᵥ ell μE K bx X ω :=
  empPair_cellFun hK hKb bx (histCoef X bx ω) X ω

end

/-- Eq. (A.9) on the torus grid. -/
theorem rJ_bound {d : ℕ} (K : LogGas.Torus.T d → LogGas.Torus.T d → ℝ)
    (hK : Continuous (Function.uncurry K)) (κ : ℝ) (hκ : 0 < κ) :
    ∃ (J : ℕ) (hJ : 0 < J), ∀ x y, |rJ (LogGas.Torus.grid d J hJ) K x y| ≤ κ :=
  LogGas.Torus.rJ_small K hK κ hκ

end LogGas.Bulk

namespace LogGas.Physical

open LogGas.Torus

/-- `A_b < ∞` for `b < 2d` with the Euclidean torus radius. -/
theorem log_exp_integrable {d : ℕ} (hd : 1 ≤ d) (r α : ℝ) (hr : 0 < r) (hα : 0 ≤ α)
    (hαd : α < d) :
    Integrable (fun z : LogGas.Torus.T d =>
      Real.exp (α * max 0 (Real.log (r / LogGas.Torus.radius z)))) (LogGas.Torus.unif d) := by
  have hF := integrable_exp_log_sing (unif d) d ((2 : ℝ) ^ d) r α hr hα hαd
    (fun ρ hρ => ball_vol d ρ hρ)
  have hm : Measurable (fun z : T d => Real.exp (α * max 0 (Real.log (r / radius z)))) :=
    Real.measurable_exp.comp
      ((measurable_const.max (Real.measurable_log.comp
        (continuous_radius.measurable.const_div r))).const_mul α)
  refine hF.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hd0 : (0 : ℝ) ≤ dist z 0 := dist_nonneg
  have hr0 : 0 ≤ radius z := Real.sqrt_nonneg _
  rcases hr0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [div_zero, Real.log_zero, max_self, mul_zero, Real.exp_zero]
    apply Real.one_le_exp
    exact mul_nonneg hα (le_max_left _ _)
  · have hdist : 0 < dist z 0 := by
      by_contra hneg
      have : dist z 0 = 0 := le_antisymm (not_lt.mp hneg) hd0
      have := radius_le_sqrt_mul z
      rw [‹dist z 0 = 0›, mul_zero] at this
      linarith
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hα
    apply max_le_max le_rfl
    apply Real.log_le_log (div_pos hr hpos)
    exact div_le_div_of_nonneg_left hr.le hdist (dist_zero_le_radius z)

end LogGas.Physical

namespace LogGas.Main

open LogGas.Torus

/-- M3: parameter choice for the bad-event term (`eq:physical-bad-probability`, audit E9). -/
theorem parameter_choice {d : ℕ} (hd : 2 ≤ d) (g : LogGas.Torus.T d → ℝ) (hg : Measurable g)
    (hcut : LogGas.Spec.cutoff g) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβd : β₀ < 2 * d) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (J₁ : ℕ) (C : ℕ → ℝ), ∀ (J : ℕ) (hJ : 0 < J), J₁ ≤ J → ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ,
      0 ≤ β → β ≤ β₀ →
      ∫⁻ x, (LogGas.BadEvent.badEvent (fun i (y : Fin N → LogGas.Torus.T d) => y i)
          (LogGas.Torus.grid d J hJ) δ).indicator
        (fun x => ENNReal.ofReal (Real.exp ((β / 2) * LogGas.Spec.energy g N x))) x
        ∂(MeasureTheory.Measure.pi fun _ : Fin N => LogGas.Torus.unif d)
        ≤ ENNReal.ofReal (C J) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨s, s', hs, hsβ⟩ := exists_conj_lt β₀ (2 * d) hβ₀ hβd
  set b' : ℝ := (s * β₀ + 2 * d) / 2 with hb'
  have hb'0 : 0 < b' := by
    have : 0 ≤ s * β₀ := mul_nonneg hs.pos.le hβ₀
    have : (0 : ℝ) < 2 * d := by positivity
    rw [hb']; linarith
  have hsb : s * β₀ ≤ b' := by rw [hb']; linarith
  have hb'd : b' < 2 * d := by rw [hb']; linarith
  obtain ⟨Cc, -, h⟩ := hcut
  obtain ⟨s₃, b₃, -, -, hb₃, -, -, hgab, -, -, hlog, -⟩ := h 3 le_rfl
  obtain ⟨A, hA1, hA⟩ := LogGas.Physical.exp_slice_bound hd1 g b₃ s₃ hg hb₃
    (∫ z, s₃ z ∂unif d) (1 / (2 * ((3 : ℕ) : ℝ))) (by norm_num) hgab hlog b' hb'0 hb'd
  obtain ⟨J₁, hJ₁⟩ := bad_term hd1 g hg b' A hb'0 hA1 (fun x => (hA x).1) (fun x => (hA x).2)
    s s' hs β₀ hβ₀ hsb δ hδ0 hδ1
  exact ⟨J₁, fun J => (((J ^ d : ℕ) : ℝ) ^ (1 / s')), hJ₁⟩

end LogGas.Main

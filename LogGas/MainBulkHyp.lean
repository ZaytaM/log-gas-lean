import LogGas.SpecAE
import LogGas.Bulk

/-!
# H1 and H2 imply the bulk-kernel hypotheses

For the bulk kernel `K(x,y) = b(x - y)` with `b` continuous, even, centered, positive and
dominated by `g` on bounded test functions, the bounded-density form of H1 for `g` with
constant `B` yields `Bulk.KHyp` with the same `B` (eq. (4.1); `notes/sec2-cutoff.tex`,
H2 bulk positivity/domination; audit C8, C9).
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus

namespace LogGas.Main

theorem bulk_hypothesis {d : ℕ} {g b : T d → ℝ} {B : ℝ} (hB : 0 < B)
    (hH1 : LogGas.Spec.boundedH1 g B) (hb : Continuous b) (hbe : ∀ x, b (-x) = b x)
    (hb0 : ∫ x, b x ∂unif d = 0) (hpos : LogGas.Spec.positive b)
    (hdom : ∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      LogGas.Spec.quadratic (fun x y => b (x - y)) f ≤
        LogGas.Spec.quadratic (fun x y => g (x - y)) f) :
    ∃ CK : ℝ, LogGas.Bulk.KHyp (unif d) (fun x y => b (x - y)) CK B := by
  obtain ⟨CK, hCK⟩ := (isCompact_univ (X := T d)).exists_bound_of_continuousOn hb.continuousOn
  refine ⟨CK, ?_, ?_, fun x y => hCK _ (Set.mem_univ _), ?_, ?_, hB, ?_⟩
  · exact (hb.comp (continuous_fst.sub continuous_snd)).measurable
  · intro x y
    rw [← hbe (y - x)]; congr 1; abel
  · intro x
    rw [integral_sub_left_eq_self (fun z => b z) (μ := unif d) x]
    exact hb0
  · intro f hf hbd
    exact hpos f hf hbd
  · intro ρ hρ hbd hnn hint
    have hm : Measurable (fun x => ρ x - 1) := hρ.sub measurable_const
    obtain ⟨C, hC⟩ := hbd
    have hbd' : ∃ C : ℝ, ∀ x, |ρ x - 1| ≤ C :=
      ⟨C + 1, fun x => (abs_sub _ _).trans (by simpa using add_le_add_right (hC x) 1)⟩
    have h1 := hH1 ρ hρ ⟨C, hC⟩ hnn hint
    have h2 := hdom _ hm hbd'
    have h3 : (B / 2) * LogGas.Spec.quadratic (fun x y => b (x - y)) (fun x => ρ x - 1) ≤
        (B / 2) * LogGas.Spec.quadratic (fun x y => g (x - y)) (fun x => ρ x - 1) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    exact h3.trans h1

end LogGas.Main

import LogGas.MainBulkHyp
import LogGas.BulkTorus

/-!
# Bulk factor of the good-event Hölder split

Lemma 4.1 (notes/sec4-bulk.tex) applied to the bulk part `b_r` of H2 with the same `B`
(contracts M2; audit C8, C9, D1): `bulk_factor`.  Mirrors the proof of `LogGas.Spec.bulk`.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LogGas.Torus LogGas.Spec
open scoped ENNReal NNReal

namespace LogGas.Main

theorem bulk_factor {d : ℕ} {g b : T d → ℝ} {B : ℝ} (hB : 0 < B)
    (hH1 : LogGas.Spec.boundedH1 g B) (hb : Continuous b) (hbe : ∀ x, b (-x) = b x)
    (hb0 : ∫ x, b x ∂unif d = 0) (hpos : LogGas.Spec.positive b)
    (hdom : ∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      LogGas.Spec.quadratic (fun x y => b (x - y)) f ≤
        LogGas.Spec.quadratic (fun x y => g (x - y)) f)
    (β₁ : ℝ) (hβ₁ : 0 ≤ β₁) (hβ₁B : β₁ < B) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₁ →
      ∫⁻ x, ENNReal.ofReal (Real.exp ((β / 2) * LogGas.Spec.energy b N x))
        ∂(Measure.pi fun _ : Fin N => unif d) ≤ ENNReal.ofReal C := by
  obtain ⟨CK, hKH⟩ := bulk_hypothesis hB hH1 hb hbe hb0 hpos hdom
  have hK : Continuous (Function.uncurry fun x y : T d => b (x - y)) :=
    hb.comp (continuous_fst.sub continuous_snd)
  obtain ⟨C, hC0, hC⟩ := LogGas.Bulk.lemma41 hKH
    (fun κ hκ => by
      obtain ⟨J, hJ, h⟩ := rJ_small (fun x y : T d => b (x - y)) hK κ hκ
      exact ⟨J ^ d, grid d J hJ, h⟩) β₁ hβ₁ hβ₁B
  refine ⟨C, fun N hN β hβ hββ₁ => ?_⟩
  have hmp : ∀ i : Fin N, MeasurePreserving (fun x : Fin N → T d => x i)
      (Measure.pi fun _ => unif d) (unif d) := fun i =>
    measurePreserving_eval (fun _ : Fin N => unif d) i
  obtain ⟨hint, hbd⟩ := hC (Measure.pi fun _ : Fin N => unif d) hN (fun i x => x i)
    (fun i => measurable_pi_apply i)
    (iIndepFun_pi (μ := fun _ : Fin N => unif d) (X := fun _ => id)
      (fun i => aemeasurable_id))
    (fun i => (hmp i).map_eq) β hβ hββ₁
  have := (ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => (Real.exp_pos _).le)).symm
  exact this.le.trans (ENNReal.ofReal_le_ofReal hbd)

end LogGas.Main

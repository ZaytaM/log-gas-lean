import LogGas.BulkLemma41
import LogGas.BulkRemainder
import LogGas.TorusGrid

/-!
# Torus instance of Lemma 4.1 and the bulk milestone

Source: `notes/sec4-bulk.tex` Lemma 4.1, `notes/appendixA.tex` eq. (A.9), `Challenge.lean`
`bulkStatement`.

* `LogGas.Torus.rJ_small` — for a continuous kernel on `T d × T d`, the remainder `r_J` of the grid
  `grid d J hJ` is uniformly `≤ κ` for `J` large (uniform continuity + `rJ_abs_le_osc`).
* `LogGas.Torus.khyp_of_continuous` — `KHyp (unif d) K CK B` from the hypotheses of `bulkStatement`
  (in the bounded-density form of H1).
* `LogGas.Spec.bulk` — `LogGas.Spec.bulkStatement`, via the abstract `LogGas.Bulk.lemma41`
  applied to the coordinate projections on `Fin N → T d`.

No deviations from the stated interface.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LogGas.Torus

theorem rJ_small {d : ℕ} (K : T d → T d → ℝ) (hK : Continuous (Function.uncurry K)) (κ : ℝ)
    (hκ : 0 < κ) :
    ∃ (J : ℕ) (hJ : 0 < J), ∀ x y, |LogGas.Bulk.rJ (grid d J hJ) K x y| ≤ κ := by
  have huc := CompactSpace.uniformContinuous_of_continuous hK
  obtain ⟨η, hη, hηK⟩ := Metric.uniformContinuous_iff.1 huc (κ / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  obtain ⟨CK, hCK⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := Function.uncurry K) hK.continuousOn
  have hb : ∀ x y, |K x y| ≤ CK := fun x y => by
    simpa using hCK (x, y) (Set.mem_univ _)
  have hosc : ∀ a b, ∀ x ∈ (grid d (n + 1) (Nat.succ_pos n)).A a,
      ∀ x' ∈ (grid d (n + 1) (Nat.succ_pos n)).A a,
      ∀ y ∈ (grid d (n + 1) (Nat.succ_pos n)).A b,
      ∀ y' ∈ (grid d (n + 1) (Nat.succ_pos n)).A b, |K x y - K x' y'| ≤ κ / 4 := by
    intro a b x hx x' hx' y hy y' hy'
    have h1 := dist_lt_of_mem_grid a hx hx'
    have h2 := dist_lt_of_mem_grid b hy hy'
    have hn' : 1 / ((n + 1 : ℕ) : ℝ) < η := by simpa using hn
    have := hηK (a := (x, y)) (b := (x', y'))
      (by rw [Prod.dist_eq]; exact max_lt (h1.trans hn') (h2.trans hn'))
    rw [Real.dist_eq] at this
    exact this.le
  intro x y
  have := LogGas.Bulk.rJ_abs_le_osc (grid d (n + 1) (Nat.succ_pos n)) hK.measurable CK hb (κ / 4)
    hosc x y
  linarith

theorem khyp_of_continuous {d : ℕ} (K : T d → T d → ℝ) (hK : Continuous (Function.uncurry K))
    (hs : ∀ x y, K x y = K y x) (hc : ∀ x, ∫ y, K x y ∂unif d = 0)
    (hpos : ∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      0 ≤ LogGas.Spec.quadratic K f)
    (B : ℝ) (hB : 0 < B)
    (hH1 : ∀ ρ : T d → ℝ, Measurable ρ → (∃ C : ℝ, ∀ x, |ρ x| ≤ C) → (∀ x, 0 ≤ ρ x) →
      ∫ x, ρ x ∂unif d = 1 →
      (B / 2) * LogGas.Spec.quadratic K (fun x => ρ x - 1) ≤ LogGas.Spec.entropy ρ) :
    ∃ CK : ℝ, LogGas.Bulk.KHyp (unif d) K CK B := by
  obtain ⟨CK, hCK⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := Function.uncurry K) hK.continuousOn
  exact ⟨CK, { meas := hK.measurable
               symm := hs
               bdd := fun x y => by simpa using hCK (x, y) (Set.mem_univ _)
               centered := hc
               pos := hpos
               B_pos := hB
               entropy := hH1 }⟩

end LogGas.Torus

namespace LogGas.Spec
open LogGas.Torus

theorem bulk : LogGas.Spec.bulkStatement := by
  intro d _ K B β0 hK hs hc hpos hB hβ0 hβB hH1
  have hH1' : ∀ ρ : T d → ℝ, Measurable ρ → (∃ C : ℝ, ∀ x, |ρ x| ≤ C) → (∀ x, 0 ≤ ρ x) →
      ∫ x, ρ x ∂unif d = 1 →
      (B / 2) * quadratic K (fun x => ρ x - 1) ≤ entropy ρ := by
    intro ρ hm ⟨C, hC⟩ h0 h1
    refine hH1 ρ ⟨hm, ae_of_all _ h0, ?_, h1, ?_⟩
    · exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun x => by
        simpa using hC x)
    · obtain ⟨C', hC'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := |C|)).exists_bound_of_continuousOn
        Real.continuous_mul_log.continuousOn
      refine Integrable.of_bound ((Real.continuous_mul_log.measurable.comp hm).aestronglyMeasurable)
        C' (ae_of_all _ fun x => ?_)
      have := hC' (ρ x) ⟨h0 x, (le_abs_self _).trans ((hC x).trans (le_abs_self C))⟩
      simpa using this
  obtain ⟨CK, hKH⟩ := khyp_of_continuous K hK hs hc hpos B hB hH1'
  obtain ⟨C, hC0, hC⟩ := LogGas.Bulk.lemma41 hKH
    (fun κ hκ => by
      obtain ⟨J, hJ, h⟩ := rJ_small K hK κ hκ
      exact ⟨J ^ d, grid d J hJ, h⟩) β0 hβ0 hβB
  refine ⟨C.toNNReal, fun N hN β hβ hββ0 => ?_⟩
  have hmp : ∀ i : Fin N, MeasurePreserving (fun x : Fin N → T d => x i)
      (Measure.pi fun _ => unif d) (unif d) := fun i =>
    measurePreserving_eval (fun _ : Fin N => unif d) i
  obtain ⟨hint, hbd⟩ := hC (Measure.pi fun _ : Fin N => unif d) hN (fun i x => x i)
    (fun i => measurable_pi_apply i)
    (iIndepFun_pi (μ := fun _ : Fin N => unif d) (X := fun _ => id)
      (fun i => aemeasurable_id))
    (fun i => (hmp i).map_eq) β hβ hββ0
  have := (ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => (Real.exp_pos _).le)).symm
  refine this.le.trans ?_
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hbd
    _ = (C.toNNReal : ℝ≥0∞) := rfl

end LogGas.Spec

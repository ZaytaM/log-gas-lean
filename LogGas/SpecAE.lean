import LogGas.TorusBase

/-!
# H1 bridges and a.e.-invariance

Bridges between the log-HLS hypotheses (`Spec.logHLS`, `PaperChallenge.LogHLS`, eq. (1.3) of
`notes/sec1-setting.tex`) and the bounded-test-function form `boundedH1`, plus invariance of the
quadratic form, `boundedH1` and the partition function under a.e. modification of `g`
(audit items C3, D1, A9/F5, G6).
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus
open scoped BigOperators ENNReal NNReal

namespace LogGas.Spec

def boundedH1 {d : ℕ} (g : T d → ℝ) (B : ℝ) : Prop :=
  ∀ ρ : T d → ℝ, Measurable ρ → (∃ C : ℝ, ∀ x, |ρ x| ≤ C) → (∀ x, 0 ≤ ρ x) →
    (∫ x, ρ x ∂unif d) = 1 →
    (B / 2) * quadratic (fun x y => g (x - y)) (fun x => ρ x - 1) ≤ entropy ρ

noncomputable def logEnergy {d : ℕ} (g : T d → ℝ) (ρ : T d → ℝ) : ℝ :=
  ∫ z, g (z.1 - z.2) * (ρ z.1 - 1) * (ρ z.2 - 1) ∂(unif d).prod (unif d)

def paperLogHLS {d : ℕ} (g : T d → ℝ) (B : ℝ) : Prop :=
  ∀ ρ : T d → ℝ, density ρ → (B / 2) * logEnergy g ρ ≤ entropy ρ

private theorem specae_density {d : ℕ} (ρ : T d → ℝ) (hρ : Measurable ρ)
    (hb : ∃ C : ℝ, ∀ x, |ρ x| ≤ C) (hnn : ∀ x, 0 ≤ ρ x) (hint : (∫ x, ρ x ∂unif d) = 1) :
    density ρ := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨hρ, Filter.Eventually.of_forall hnn, Integrable.of_bound hρ.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa using hC x), hint, ?_⟩
  have hcont : Continuous fun x : ℝ => x * Real.log x := Real.continuous_mul_log
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := C)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine Integrable.of_bound (hcont.measurable.comp hρ).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => ?_)
  have := hM (ρ x) ⟨hnn x, (le_abs_self _).trans (hC x)⟩
  simpa using this

theorem boundedH1_of_logHLS {d : ℕ} {g : T d → ℝ} {B : ℝ} (h : logHLS g B) :
    boundedH1 g B := fun ρ hρ hb hnn hint =>
  (h ρ (specae_density ρ hρ hb hnn hint)).2

theorem integrable_logEnergy_integrand {d : ℕ} {g : T d → ℝ} (hg : Integrable g (unif d))
    (ρ : T d → ℝ) (hρ : Measurable ρ) (C : ℝ) (hC : ∀ x, |ρ x| ≤ C) :
    Integrable (fun z : T d × T d => g (z.1 - z.2) * (ρ z.1 - 1) * (ρ z.2 - 1))
      ((unif d).prod (unif d)) := by
  have hgi : Integrable (fun z : T d × T d => g (z.1 - z.2)) ((unif d).prod (unif d)) :=
    (measurePreserving_sub d).integrable_comp_of_integrable hg
  have hm1 : Measurable fun z : T d × T d => ρ z.1 - 1 := (hρ.comp measurable_fst).sub_const 1
  have hm2 : Measurable fun z : T d × T d => ρ z.2 - 1 := (hρ.comp measurable_snd).sub_const 1
  have hb : ∀ x, |ρ x - 1| ≤ |C| + 1 := fun x => by
    calc |ρ x - 1| ≤ |ρ x| + |(1:ℝ)| := abs_sub _ _
      _ ≤ |C| + 1 := by
        have := hC x
        simp only [abs_one]
        linarith [le_abs_self C]
  refine Integrable.mono' (hgi.norm.mul_const ((|C| + 1) * (|C| + 1)))
    ((hgi.aestronglyMeasurable.mul hm1.aestronglyMeasurable).mul hm2.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  have h0 : 0 ≤ |C| + 1 := by positivity
  calc |g (z.1 - z.2)| * |ρ z.1 - 1| * |ρ z.2 - 1|
      ≤ |g (z.1 - z.2)| * (|C| + 1) * (|C| + 1) := by gcongr <;> exact hb _
    _ = |g (z.1 - z.2)| * ((|C| + 1) * (|C| + 1)) := by ring

theorem logEnergy_eq_quadratic {d : ℕ} {g : T d → ℝ} (hg : Integrable g (unif d))
    (ρ : T d → ℝ) (hρ : Measurable ρ) (C : ℝ) (hC : ∀ x, |ρ x| ≤ C) :
    logEnergy g ρ = quadratic (fun x y => g (x - y)) (fun x => ρ x - 1) := by
  unfold logEnergy quadratic
  exact integral_prod _ (integrable_logEnergy_integrand hg ρ hρ C hC) |>.trans (by
    congr 1)

theorem boundedH1_of_paperLogHLS {d : ℕ} {g : T d → ℝ} {B : ℝ} (hg : Integrable g (unif d))
    (h : paperLogHLS g B) : boundedH1 g B := fun ρ hρ hb hnn hint => by
  obtain ⟨C, hC⟩ := hb
  rw [← logEnergy_eq_quadratic hg ρ hρ C hC]
  exact h ρ (specae_density ρ hρ ⟨C, hC⟩ hnn hint)

theorem quadratic_congr_ae {d : ℕ} {g g' : T d → ℝ} (h : g =ᵐ[unif d] g') (f : T d → ℝ) :
    quadratic (fun x y => g (x - y)) f = quadratic (fun x y => g' (x - y)) f := by
  unfold quadratic
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae ?_
  have hmp : MeasurePreserving (fun y : T d => x - y) (unif d) (unif d) :=
    Measure.measurePreserving_sub_left (unif d) x
  filter_upwards [hmp.quasiMeasurePreserving.ae h] with y hy
  rw [hy]

theorem boundedH1_congr_ae {d : ℕ} {g g' : T d → ℝ} (h : g =ᵐ[unif d] g') {B : ℝ} :
    boundedH1 g B ↔ boundedH1 g' B := by
  unfold boundedH1
  simp only [quadratic_congr_ae h]

theorem ae_pair_sub {d N : ℕ} {P : T d → Prop} (h : ∀ᵐ z ∂unif d, P z) (i j : Fin N)
    (hij : i ≠ j) : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => unif d), P (x i - x j) := by
  have hI := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N => unif d)
    (X := fun _ => (id : T d → T d)) (fun _ => aemeasurable_id)
  have hind := hI.indepFun hij
  have hei := measurePreserving_eval (fun _ : Fin N => unif d) i
  have hej := measurePreserving_eval (fun _ : Fin N => unif d) j
  have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hei.measurable.aemeasurable hej.measurable.aemeasurable).1 hind
  have hmp : MeasurePreserving (fun x : Fin N → T d => (x i, x j))
      (Measure.pi fun _ : Fin N => unif d) ((unif d).prod (unif d)) := by
    refine ⟨hei.measurable.prodMk hej.measurable, ?_⟩
    rw [hmap, hei.map_eq, hej.map_eq]
  exact ((measurePreserving_sub d).comp hmp).quasiMeasurePreserving.ae h

theorem partition_congr_ae {d : ℕ} {g g' : T d → ℝ} (h : g =ᵐ[unif d] g') (N : ℕ) (β : ℝ) :
    partition g N β = partition g' N β := by
  unfold partition
  refine lintegral_congr_ae ?_
  have hall : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => unif d),
      ∀ i j : Fin N, i ≠ j → g (x i - x j) = g' (x i - x j) := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun x hne => absurd hij hne
    · filter_upwards [ae_pair_sub h i j hij] with x hx _ using hx
  filter_upwards [hall] with x hx
  have : energy g N x = energy g' N x := by
    unfold energy
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact hx i j (Finset.ne_of_mem_erase hj).symm
  simp only [weight, this]

end LogGas.Spec

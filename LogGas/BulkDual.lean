import LogGas.Bulk

/-!
# Dual log-HLS (A.5)

Source: `notes/appendixA.tex`, eq. `eq:dual-log-hls` (A.5); audit E6 A3.

For a bounded measurable `h`, `log ∫ exp(T_K h) dμ ≤ ⟨h, T_K h⟩ / (2B)`.  Proof: the Gibbs
density `ρ = e^{T h}/Z` gives `∫ ρ log ρ = ∫ (T h) ρ − log Z` (`Bulk.gibbs_identity`); the entropy
hypothesis bounds this below by `(B/2)⟨ρ−1, ρ−1⟩`; `∫ (T h) ρ = ⟨h, ρ−1⟩` by centering; and the
square `⟨u − h/B, u − h/B⟩ ≥ 0` is completed.

Targets: `measurable_T`, `dual_log_hls`, `integral_exp_T_le`.  No deviations from the stated
interfaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

section Dual

variable {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE]

/-- bounded measurable functions -/
private def BDM (f : E → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C

/-- jointly bounded measurable integrands -/
private def JB (F : E → E → ℝ) : Prop :=
  Measurable (uncurry F) ∧ ∃ C, ∀ x y, |F x y| ≤ C

private lemma BDM.sub {f g : E → ℝ} (hf : BDM f) (hg : BDM g) : BDM (f - g) := by
  obtain ⟨hf1, a, ha⟩ := hf
  obtain ⟨hg1, b, hb⟩ := hg
  refine ⟨hf1.sub hg1, a + b, fun x => ?_⟩
  simp only [Pi.sub_apply]
  calc |f x - g x| = |f x + -g x| := by rw [sub_eq_add_neg]
    _ ≤ |f x| + |-g x| := abs_add_le _ _
    _ ≤ a + b := by rw [abs_neg]; exact add_le_add (ha x) (hb x)

private lemma BDM.smul {f : E → ℝ} (c : ℝ) (hf : BDM f) : BDM (c • f) := by
  obtain ⟨hf1, a, ha⟩ := hf
  refine ⟨hf1.const_smul c, |c| * a, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (ha x) (abs_nonneg c)

private lemma JB.slice {F : E → E → ℝ} (hF : JB F) (x : E) : Integrable (F x) μE := by
  obtain ⟨hm, C, hC⟩ := hF
  refine Integrable.of_bound (C := C) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (hm.comp (measurable_prodMk_left (x := x))).aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using hC x y

private lemma JB.integrable {F : E → E → ℝ} (hF : JB F) :
    Integrable (uncurry F) (μE.prod μE) := by
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound (C := C) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs, uncurry] using hC p.1 p.2)

private lemma JB.sub {F G : E → E → ℝ} (hF : JB F) (hG : JB G) :
    ∫ x, ∫ y, (F x y - G x y) ∂μE ∂μE = ∫ x, ∫ y, F x y ∂μE ∂μE - ∫ x, ∫ y, G x y ∂μE ∂μE := by
  have h1 : ∀ x, ∫ y, (F x y - G x y) ∂μE = ∫ y, F x y ∂μE - ∫ y, G x y ∂μE :=
    fun x => integral_sub (hF.slice x) (hG.slice x)
  simp_rw [h1]
  exact integral_sub hF.integrable.integral_prod_left hG.integrable.integral_prod_left

private lemma JB_kfg {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) {f g : E → ℝ}
    (hf : BDM f) (hg : BDM g) : JB (fun x y => K x y * f x * g y) := by
  obtain ⟨hf1, a, ha⟩ := hf
  obtain ⟨hg1, b, hb⟩ := hg
  have hK' : Measurable fun p : E × E => K p.1 p.2 := hK.meas
  refine ⟨?_, |CK| * |a| * |b|, fun x y => ?_⟩
  · show Measurable fun p : E × E => K p.1 p.2 * f p.1 * g p.2
    exact (hK'.mul (hf1.comp measurable_fst)).mul (hg1.comp measurable_snd)
  · rw [abs_mul, abs_mul]
    have h1 : |K x y| ≤ |CK| := (hK.bdd x y).trans (le_abs_self _)
    have h2 : |f x| ≤ |a| := (ha x).trans (le_abs_self _)
    have h3 : |g y| ≤ |b| := (hb y).trans (le_abs_self _)
    gcongr

private lemma energy_sub_left {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B)
    {f1 f2 g : E → ℝ} (h1 : BDM f1) (h2 : BDM f2) (hg : BDM g) :
    energy μE K (f1 - f2) g = energy μE K f1 g - energy μE K f2 g := by
  unfold energy
  have key : ∀ x y, K x y * (f1 - f2) x * g y = K x y * f1 x * g y - K x y * f2 x * g y := by
    intro x y; simp only [Pi.sub_apply]; ring
  simp_rw [key]
  exact JB.sub (JB_kfg hK h1 hg) (JB_kfg hK h2 hg)

private lemma energy_sub_right {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B)
    {f g1 g2 : E → ℝ} (hf : BDM f) (h1 : BDM g1) (h2 : BDM g2) :
    energy μE K f (g1 - g2) = energy μE K f g1 - energy μE K f g2 := by
  unfold energy
  have key : ∀ x y, K x y * f x * (g1 - g2) y = K x y * f x * g1 y - K x y * f x * g2 y := by
    intro x y; simp only [Pi.sub_apply]; ring
  simp_rw [key]
  exact JB.sub (JB_kfg hK hf h1) (JB_kfg hK hf h2)

private lemma energy_smul_left' {K : E → E → ℝ} (c : ℝ) (f g : E → ℝ) :
    energy μE K (c • f) g = c * energy μE K f g := by
  unfold energy
  have key : ∀ x y, K x y * (c • f) x * g y = c * (K x y * f x * g y) := by
    intro x y; simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [key, integral_const_mul]

private lemma energy_smul_right' {K : E → E → ℝ} (c : ℝ) (f g : E → ℝ) :
    energy μE K f (c • g) = c * energy μE K f g := by
  unfold energy
  have key : ∀ x y, K x y * f x * (c • g) y = c * (K x y * f x * g y) := by
    intro x y; simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [key, integral_const_mul]

private lemma energy_comm {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B)
    {f g : E → ℝ} (hf : BDM f) (hg : BDM g) :
    energy μE K f g = energy μE K g f := by
  unfold energy
  rw [integral_integral_swap (JB_kfg hK hf hg).integrable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hK.symm x y]; ring

/-- `T_K h` is measurable. -/
theorem measurable_T (K : E → E → ℝ) (hK : Measurable (uncurry K)) (h : E → ℝ)
    (hh : Measurable h) : Measurable (T μE K h) := by
  have hK' : Measurable fun p : E × E => K p.1 p.2 := hK
  have hm : Measurable (uncurry fun x y => K x y * h y) :=
    hK'.mul (hh.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := μE)).measurable

private lemma abs_T_le {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) {h : E → ℝ} {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (x : E) : |T μE K h x| ≤ |CK| * |C| := by
  unfold T
  have : ‖∫ y, K x y * h y ∂μE‖ ≤ |CK| * |C| * μE.real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hK.bdd x y).trans (le_abs_self _)) ((hC y).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _))
  simpa [Real.norm_eq_abs] using this

/-- Eq. `eq:dual-log-hls` (A.5). -/
theorem dual_log_hls {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) (h : E → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : ∀ x, |h x| ≤ C) :
    Real.log (∫ x, Real.exp (T μE K h x) ∂μE) ≤ energy μE K h h / (2 * B) := by
  have hB := hK.B_pos
  set f := T μE K h with hfdef
  have hfm : Measurable f := measurable_T K hK.meas h hh
  set D := |CK| * |C| with hD
  have hfD : ∀ x, |f x| ≤ D := abs_T_le hK hC
  have hexp : Integrable (fun x => Real.exp (f x)) μE := by
    refine Integrable.of_bound (C := Real.exp D) (Real.measurable_exp.comp hfm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (hfD x))
  set Z := ∫ y, Real.exp (f y) ∂μE with hZ
  have hZ0 : 0 < Z := integral_exp_pos hexp
  set ρ : E → ℝ := fun x => Real.exp (f x) / Z with hρ
  have hρm : Measurable ρ := (Real.measurable_exp.comp hfm).div_const Z
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (div_pos (Real.exp_pos _) hZ0).le
  have hρb : ∀ x, |ρ x| ≤ Real.exp D / Z := by
    intro x
    rw [abs_of_nonneg (hρ0 x)]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (le_trans (le_abs_self _) (hfD x))) hZ0.le
  have hρ1 : ∫ x, ρ x ∂μE = 1 := by
    simp only [hρ]; rw [integral_div, ← hZ, div_self hZ0.ne']
  have hent := hK.entropy ρ hρm ⟨_, hρb⟩ hρ0 hρ1
  have hgibbs := gibbs_identity μE f hfm D hfD
  -- bounded measurable ingredients
  have hBh : BDM h := ⟨hh, C, hC⟩
  have hBρ : BDM ρ := ⟨hρm, _, hρb⟩
  have hB1 : BDM (fun _ : E => (1 : ℝ)) := ⟨measurable_const, 1, fun _ => by simp⟩
  set u : E → ℝ := ρ - fun _ => 1 with hu
  have hBu : BDM u := BDM.sub hBρ hB1
  have hu' : (fun x => ρ x - 1) = u := rfl
  rw [hu'] at hent
  -- ∫ f ρ = energy h ρ
  have hfρ : ∫ x, f x * ρ x ∂μE = energy μE K h ρ := by
    unfold energy
    rw [integral_integral_swap (JB_kfg hK hBh hBρ).integrable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, T]
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hK.symm y x]
  -- energy h 1 = 0
  have h1 : energy μE K h (fun _ => 1) = 0 := by
    unfold energy
    have : ∀ x, ∫ y, K x y * h x * 1 ∂μE = 0 := by
      intro x
      simp only [mul_one]
      rw [integral_mul_const, hK.centered x, zero_mul]
    exact (integral_congr_ae (Filter.Eventually.of_forall this)).trans (by simp)
  have hhu : energy μE K h u = energy μE K h ρ := by
    have := energy_sub_right hK hBh hBρ hB1
    simp only [hu]
    rw [this, h1, sub_zero]
  have hcomm : energy μE K u h = energy μE K h u := energy_comm hK hBu hBh
  -- completing the square
  set c : ℝ := 1 / B with hc
  have hcB : B * c = 1 := by rw [hc]; field_simp
  have hBch : BDM (c • h) := hBh.smul c
  have hBv : BDM (u - c • h) := hBu.sub hBch
  have hpos := hK.pos (u - c • h) hBv.1 hBv.2
  have e1 := energy_sub_left hK hBu hBch hBv
  have e2 := energy_sub_right hK hBu hBu hBch
  have e3 := energy_sub_right hK hBch hBu hBch
  have s1 := energy_smul_right' (μE := μE) (K := K) c u h
  have s2 := energy_smul_left' (μE := μE) (K := K) c h u
  have s3 := energy_smul_left' (μE := μE) (K := K) c h (c • h)
  have s4 := energy_smul_right' (μE := μE) (K := K) c h h
  have hcomm' : energy μE K h u = energy μE K u h := hcomm.symm
  set Euu := energy μE K u u
  set Ehh := energy μE K h h
  set S := energy μE K h u
  have hsq : 0 ≤ Euu - 2 * c * S + c * c * Ehh := by
    rw [e1, e2, e3, s1, s2, s3, s4] at hpos
    rw [hcomm] at hpos
    linarith
  have hlogρ : Real.log Z ≤ S - (B / 2) * Euu := by
    have := hgibbs
    rw [hfρ] at this
    have hρ' : (fun x => ρ x * Real.log (ρ x)) = fun x => (Real.exp (f x) / Z) * Real.log (Real.exp (f x) / Z) := rfl
    have hent' : (B / 2) * Euu ≤ ∫ x, (Real.exp (f x) / Z) * Real.log (Real.exp (f x) / Z) ∂μE := hent
    linarith
  have key : (B / 2) * (Euu - 2 * c * S + c * c * Ehh) = (B / 2) * Euu - S + Ehh / (2 * B) := by
    rw [hc]; field_simp
  have := mul_nonneg (by linarith : 0 ≤ B / 2) hsq
  linarith

/-- Integrability and the exponential-moment bound. -/
theorem integral_exp_T_le {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B) (h : E → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : ∀ x, |h x| ≤ C) :
    Integrable (fun x => Real.exp (T μE K h x)) μE ∧
      ∫ x, Real.exp (T μE K h x) ∂μE ≤ Real.exp (energy μE K h h / (2 * B)) := by
  have hfm : Measurable (T μE K h) := measurable_T K hK.meas h hh
  have hfD : ∀ x, |T μE K h x| ≤ |CK| * |C| := abs_T_le hK hC
  have hexp : Integrable (fun x => Real.exp (T μE K h x)) μE := by
    refine Integrable.of_bound (C := Real.exp (|CK| * |C|))
      (Real.measurable_exp.comp hfm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (hfD x))
  refine ⟨hexp, ?_⟩
  have hZ0 : 0 < ∫ x, Real.exp (T μE K h x) ∂μE := integral_exp_pos hexp
  exact (Real.log_le_iff_le_exp hZ0).1 (dual_log_hls hK h hh C hC)

end Dual

end LogGas.Bulk

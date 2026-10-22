import LogGas.BulkSplit
import LogGas.BulkRemainder
import LogGas.BulkCoarse

/-!
# Lemma 4.1 (`lem:continuous-entropy-partition`), abstract form

Source: `notes/appendixA.tex`, eqs. (A.10), (A.11); `notes/sec4-bulk.tex` Lemma 4.1.

* `lemma41` — for a kernel satisfying `KHyp` that can be approximated by grids with arbitrarily
  small remainder `rJ`, and `0 ≤ β₀ < B`, there is a constant `C` such that for every `N ≥ 1`,
  every i.i.d. sample `X` with law `μE` and every `0 ≤ β ≤ β₀`,
  `exp((β/2) W_N(K))` is integrable with `𝔼 exp((β/2) W_N(K)) ≤ C`.

Proof: `W_le_coarse` splits `W K ≤ N·coarse + M² + W(rJ) + 5 CK`; Hölder with conjugate exponents
`p, q` separates the coarse part (`coarse_exp_bound`, exponent `pβ < B`) from the remainder
(`rJ_exp_bound`, exponent `qβ`, with `Cu·κ·qβ₀ ≤ 1/2`).

No deviations from the stated interface.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function Matrix
open scoped BigOperators ENNReal

namespace LogGas.Bulk

open LogGas.Decoupling LogGas.BadEvent LogGas.Singular

private theorem l41_holder {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p q : ℝ} (hpq : p.HolderConjugate q) {f g : Ω → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfi : Integrable (fun ω => f ω ^ p) μ) (hgi : Integrable (fun ω => g ω ^ q) μ) :
    Integrable (fun ω => f ω * g ω) μ ∧
      ∫ ω, f ω * g ω ∂μ ≤ (∫ ω, f ω ^ p ∂μ) ^ (1 / p) * (∫ ω, g ω ^ q ∂μ) ^ (1 / q) := by
  have key : ∀ {r : ℝ} {h : Ω → ℝ}, 0 < r → Measurable h → (∀ ω, 0 ≤ h ω) →
      Integrable (fun ω => h ω ^ r) μ → MemLp h (ENNReal.ofReal r) μ := by
    intro r h hr hh hh0 hi
    have hne : ENNReal.ofReal r ≠ 0 := by simpa using hr
    have hnt : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
    refine (memLp_norm_rpow_iff (p := ENNReal.ofReal r) hh.aestronglyMeasurable hne hnt).1 ?_
    rw [ENNReal.div_self hne hnt, memLp_one_iff_integrable]
    refine hi.congr (ae_of_all _ fun ω => ?_)
    simp only [ENNReal.toReal_ofReal hr.le, Real.norm_of_nonneg (hh0 ω)]
  have hf := key hpq.pos hfm hf0 hfi
  have hg := key hpq.symm.pos hgm hg0 hgi
  refine ⟨?_, integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ hf0) (ae_of_all _ hg0) hf hg⟩
  haveI := hpq.ennrealOfReal
  exact hf.integrable_mul hg

theorem lemma41 {E : Type*} [MeasurableSpace E] {μE : Measure E} [IsProbabilityMeasure μE]
    {K : E → E → ℝ} {CK B : ℝ} (hK : KHyp μE K CK B)
    (hgrid : ∀ κ : ℝ, 0 < κ → ∃ (M : ℕ) (bx : Boxes μE M), ∀ x y, |rJ bx K x y| ≤ κ)
    (β₀ : ℝ) (hβ0 : 0 ≤ β₀) (hβB : β₀ < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {N : ℕ}, 1 ≤ N → ∀ (X : Fin N → Ω → E), (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i, μ.map (X i) = μE) → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      Integrable (fun ω => Real.exp ((β / 2) * W K X ω)) μ ∧
        ∫ ω, Real.exp ((β / 2) * W K X ω) ∂μ ≤ C := by
  have hB := hK.B_pos
  -- exponents
  set p : ℝ := 1 + (B - β₀) / (2 * B) with hp
  have hp1 : 1 < p := by rw [hp]; have : 0 < (B - β₀) / (2 * B) := by apply div_pos <;> linarith
                         linarith
  have hpβ : p * β₀ < B := by
    have h1 : (B - β₀) / (2 * B) * β₀ ≤ (B - β₀) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [mul_nonneg hβ0 (sub_nonneg.2 hβB.le)]
    have : p * β₀ = β₀ + (B - β₀) / (2 * B) * β₀ := by rw [hp]; ring
    linarith
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  set q : ℝ := p.conjExponent with hq
  have hq0 : 0 < q := hpq.symm.pos
  set κ : ℝ := 1 / (32 * q * β₀ + 1) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hκθ : Cu * κ * (q * β₀) ≤ 1 / 2 := by
    have hCu : Cu = 16 := rfl
    have e : 16 * (1 / (32 * q * β₀ + 1)) * (q * β₀) = 16 * (q * β₀) / (32 * q * β₀ + 1) := by
      field_simp
    rw [hCu, hκ, e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hq0.le hβ0]
  obtain ⟨M, bx, hbx⟩ := hgrid κ hκ0
  have hSig := gram_posSemidef hK bx
  set Cc : ℝ := (1 - p * β₀ / B) ^ (-(M : ℝ) / 2) with hCc
  have hbase : 0 < 1 - p * β₀ / B := by
    have : p * β₀ / B < 1 := (div_lt_one hB).2 hpβ
    linarith
  refine ⟨Real.exp ((β₀ / 2) * ((M : ℝ) ^ 2 + 5 * |CK|)) * Cc ^ (1 / p) * (8 / 3) ^ (1 / q),
    by positivity, ?_⟩
  intro Ω _ μ _ N hN X hXm hXi hXl β hβ0' hββ0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- measurability of `W`
  have hWm : ∀ {K' : E → E → ℝ}, Measurable (uncurry K') → Measurable (W K' X) := by
    intro K' hK'
    unfold W
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => ?_) _
    exact hK'.comp ((hXm i).prodMk (hXm j))
  have hmr := measurable_rJ bx hK.meas CK hK.bdd
  have hcm := measurable_coarse (μE := μE) K hK.meas bx (1 / (N : ℝ)) X hXm
  -- the two Hölder factors
  set f : Ω → ℝ := fun ω => Real.exp ((β / 2) * ((N : ℝ) * coarse μE K bx (1 / N) X ω)) with hf
  set g : Ω → ℝ := fun ω => Real.exp ((β / 2) * W (rJ bx K) X ω) with hg
  have hfm : Measurable f := Real.measurable_exp.comp ((hcm.const_mul (N : ℝ)).const_mul _)
  have hgm : Measurable g := Real.measurable_exp.comp ((hWm hmr).const_mul _)
  have hpβ' : p * β < B := by nlinarith
  obtain ⟨hfi, hfb⟩ := coarse_exp_bound hK bx μ hN X hXm hXi hXl (1 / (N : ℝ))
    (by positivity) (p * β) (by positivity) hpβ'
  have hfp : ∀ ω, f ω ^ p = Real.exp ((p * β * N / 2) * coarse μE K bx (1 / N) X ω) := by
    intro ω
    rw [hf, ← Real.exp_mul]; congr 1; ring
  have hfi' : Integrable (fun ω => f ω ^ p) μ := by
    refine hfi.congr (ae_of_all _ fun ω => ?_)
    simp only [hfp]
  have hfb' : ∫ ω, f ω ^ p ∂μ ≤ Cc := by
    have e : ∫ ω, f ω ^ p ∂μ
        = ∫ ω, Real.exp ((p * β * N / 2) * coarse μE K bx (1 / N) X ω) ∂μ := by
      congr 1; funext ω; exact hfp ω
    rw [e]
    refine hfb.trans ?_
    rw [hCc]
    refine Real.rpow_le_rpow_of_nonpos hbase ?_ (by
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith)
    have : p * β / B ≤ p * β₀ / B := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul_of_nonneg_left hββ0 (by linarith)
    linarith
  obtain ⟨hgi, hgb⟩ := rJ_exp_bound bx hK.meas CK hK.bdd hK.symm κ hκ0 hbx μ hN X hXm hXi hXl
    (q * β) (by positivity) (by
      have : Cu * κ * (q * β) ≤ Cu * κ * (q * β₀) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hββ0 hq0.le) (by
          have : (0 : ℝ) ≤ Cu := by norm_num [Cu]
          positivity)
      linarith)
  have hgq : ∀ ω, g ω ^ q = Real.exp ((q * β / 2) * W (rJ bx K) X ω) := by
    intro ω
    rw [hg, ← Real.exp_mul]; congr 1; ring
  have hgi' : Integrable (fun ω => g ω ^ q) μ := by
    refine hgi.congr (ae_of_all _ fun ω => ?_)
    simp only [hgq]
  have hgb' : ∫ ω, g ω ^ q ∂μ ≤ 8 / 3 := by
    have e : ∫ ω, g ω ^ q ∂μ = ∫ ω, Real.exp ((q * β / 2) * W (rJ bx K) X ω) ∂μ := by
      congr 1; funext ω; exact hgq ω
    rw [e]; exact hgb
  obtain ⟨hfgi, hfg⟩ := l41_holder μ hpq hfm hgm (fun ω => (Real.exp_pos _).le)
    (fun ω => (Real.exp_pos _).le) hfi' hgi'
  -- pointwise bound
  set c : ℝ := Real.exp ((β₀ / 2) * ((M : ℝ) ^ 2 + 5 * |CK|)) with hc
  have hpt : ∀ ω, Real.exp ((β / 2) * W K X ω) ≤ c * (f ω * g ω) := by
    intro ω
    have h1 := W_le_coarse hK.meas CK hK.bdd hK.symm bx X ω hN hSig
    have h2 : (M : ℝ) ^ 2 + 5 * CK ≤ (M : ℝ) ^ 2 + 5 * |CK| := by
      have := le_abs_self CK; linarith
    have h3 : (β / 2) * ((M : ℝ) ^ 2 + 5 * CK) ≤ (β₀ / 2) * ((M : ℝ) ^ 2 + 5 * |CK|) := by
      have h4 : (0 : ℝ) ≤ (M : ℝ) ^ 2 + 5 * |CK| := by positivity
      calc (β / 2) * ((M : ℝ) ^ 2 + 5 * CK) ≤ (β / 2) * ((M : ℝ) ^ 2 + 5 * |CK|) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (β₀ / 2) * ((M : ℝ) ^ 2 + 5 * |CK|) :=
            mul_le_mul_of_nonneg_right (by linarith) h4
    have h5 : (β / 2) * W K X ω ≤ (β₀ / 2) * ((M : ℝ) ^ 2 + 5 * |CK|)
        + (β / 2) * ((N : ℝ) * coarse μE K bx (1 / N) X ω) + (β / 2) * W (rJ bx K) X ω := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ β / 2)
      nlinarith [this, h3]
    calc Real.exp ((β / 2) * W K X ω)
        ≤ Real.exp ((β₀ / 2) * ((M : ℝ) ^ 2 + 5 * |CK|)
          + (β / 2) * ((N : ℝ) * coarse μE K bx (1 / N) X ω) + (β / 2) * W (rJ bx K) X ω) :=
          Real.exp_le_exp.2 h5
      _ = c * (f ω * g ω) := by rw [Real.exp_add, Real.exp_add, hc, hf, hg]; ring
  have hmeasW := Real.measurable_exp.comp ((hWm hK.meas).const_mul (β / 2))
  have hint : Integrable (fun ω => Real.exp ((β / 2) * W K X ω)) μ :=
    Integrable.mono' (hfgi.const_mul c) hmeasW.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, Real.exp ((β / 2) * W K X ω) ∂μ ≤ ∫ ω, c * (f ω * g ω) ∂μ :=
        integral_mono hint (hfgi.const_mul c) hpt
    _ = c * ∫ ω, f ω * g ω ∂μ := integral_const_mul _ _
    _ ≤ c * ((∫ ω, f ω ^ p ∂μ) ^ (1 / p) * (∫ ω, g ω ^ q ∂μ) ^ (1 / q)) :=
        mul_le_mul_of_nonneg_left hfg (Real.exp_pos _).le
    _ ≤ c * (Cc ^ (1 / p) * (8 / 3) ^ (1 / q)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have hI : 0 ≤ ∫ ω, f ω ^ p ∂μ := integral_nonneg fun ω => by
          have : 0 ≤ f ω := (Real.exp_pos _).le
          positivity
        have hJ : 0 ≤ ∫ ω, g ω ^ q ∂μ := integral_nonneg fun ω => by
          have : 0 ≤ g ω := (Real.exp_pos _).le
          positivity
        exact mul_le_mul (Real.rpow_le_rpow hI hfb' (by positivity))
          (Real.rpow_le_rpow hJ hgb' (by positivity)) (by positivity) (by positivity)
    _ = c * Cc ^ (1 / p) * (8 / 3) ^ (1 / q) := by ring

end LogGas.Bulk

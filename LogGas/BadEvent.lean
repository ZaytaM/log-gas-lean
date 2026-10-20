import LogGas.Warmup

/-!
# Phase 2 — Section 3 (`subsec:proof-bad-set`): discarding overcrowded boxes

Source: `notes/sec3-badevent.tex`, with the boxes of `notes/sec1-setting.tex`
(eq. `eq:common-box-partition`, `eq:physical-neighbor-events`).  Phase notes: `notes/phase2.md`.

Setting.  `(Ω, μ)` is a probability space and `X : Fin N → Ω → E` are i.i.d. with law `ν` on a
measurable additive group `E` (the torus `T^d` with normalized Lebesgue measure in the paper).
The kernel `g : E → ℝ` is measurable; the constant `A_b = ∫ e^{b g/2} dν` of the paper enters
through the hypothesis `∫ exp((b/2) g(x - y)) dν(y) ≤ A` for `ν`-a.e. `x`, together with
`1 ≤ A`.  Boxes are modelled abstractly by `Boxes ν M`: a measurable partition of `E` into `M`
sets of `ν`-measure `1/M`.

Statements (phase notes B1–B6):
* B1 is `LogGas.Warmup.jensen_avg_exp` (imported, not restated);
* B2 `rough_bound` — eq. `eq:rough-partition-bound` (3.1), `Z_{N,b} ≤ A_b^{N-1}`;
* B3 `Z_mono` — `Z_{N,γ} ≤ Z_{N,b}^{γ/b} ≤ A_b^{N-1}` for `0 ≤ γ ≤ b`;
* B4 `chernoff_binomial` — binomial Chernoff bound with relative-entropy exponent;
* B5 `bad_probability` — eq. `eq:physical-bad-probability` (3.2);
* B6 `bad_gibbs_bound` — eq. `eq:physical-bad-gibbs-bound` (3.3).

Auxiliary statements: integrability of the Gibbs weights (`integrable_exp_sum`,
`integrable_exp_W`), Jensen `1 ≤ ∫ e^K` for centered `K` (`one_le_integral_exp`), the Lyapunov
inequality (`integral_exp_mul_le_rpow`), the mgf of the occupancy (`mgf_occupancy`),
measurability of the bad event, and the Hölder step with an indicator (`holder_indicator`).

The standing hypotheses H1/H2 of `notes/hypotheses.md` are not needed in this phase.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Function
open scoped BigOperators ENNReal

namespace LogGas.BadEvent

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-! ### Definitions -/

/-- `W_N(K) = (1/N) ∑_{i ≠ j} K(X_i, X_j)` (eq. `eq:homogeneous-partition-function`), for a
two-variable kernel `K`. -/
noncomputable def W {N : ℕ} (K : E → E → ℝ) (X : Fin N → Ω → E) (ω : Ω) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ∑ j ∈ univ.erase i, K (X i ω) (X j ω)

/-- `Z_{N,β} = 𝔼[e^{(β/2) W_N(g)}]` (eq. `eq:homogeneous-partition-function`), where the
function `g` of one variable denotes the translation-invariant kernel `g(x - y)`. -/
noncomputable def Z {N : ℕ} [Sub E] (μ : Measure Ω) (β : ℝ) (g : E → ℝ)
    (X : Fin N → Ω → E) : ℝ :=
  ∫ ω, Real.exp ((β / 2) * W (fun x y => g (x - y)) X ω) ∂μ

/-- The relative entropy `D(δ‖q) = δ log(δ/q) + (1-δ) log((1-δ)/(1-q))` of two Bernoulli
laws (eq. `eq:physical-bad-probability`). -/
noncomputable def relEnt (δ q : ℝ) : ℝ :=
  δ * Real.log (δ / q) + (1 - δ) * Real.log ((1 - δ) / (1 - q))

/-- The occupancy `n_A = #{i : X_i ∈ A}` of a set `A`, written as a sum of indicators. -/
noncomputable def occupancy {N : ℕ} (X : Fin N → Ω → E) (A : Set E) (ω : Ω) : ℕ :=
  ∑ i, A.indicator 1 (X i ω)

/-- The grid of boxes (eq. `eq:common-box-partition`), abstractly: a measurable partition of
`E` into `M` sets, each of `ν`-measure `1/M`. -/
structure Boxes (ν : Measure E) (M : ℕ) where
  /-- The boxes `A_a`. -/
  A : Fin M → Set E
  meas : ∀ a, MeasurableSet (A a)
  disj : Pairwise (Disjoint on A)
  cover : ⋃ a, A a = Set.univ
  vol : ∀ a, ν (A a) = (M : ℝ≥0∞)⁻¹

/-- The bad event `𝓑_{N,J,δ}` (eq. `eq:physical-neighbor-events`): some box holds more than
`δ N` particles. -/
def badEvent {ν : Measure E} {N M : ℕ} (X : Fin N → Ω → E) (bx : Boxes ν M) (δ : ℝ) :
    Set Ω :=
  {ω | ∃ a, δ * N < (occupancy X (bx.A a) ω : ℝ)}

/-! ### Elementary facts -/

-- SKETCH: `Measure.real`, `bx.vol a`, `ENNReal.toReal_inv`, `ENNReal.toReal_natCast`,
-- `one_div`.
/-- Each box has real `ν`-measure `1/M`. -/
theorem Boxes.real_vol {ν : Measure E} {M : ℕ} (bx : Boxes ν M) (a : Fin M) :
    ν.real (bx.A a) = 1 / M := by
  simp [Measure.real, bx.vol a]

-- SKETCH: push the cast inside with `occupancy`, `Nat.cast_sum`, `Set.indicator` (the
-- real-valued indicator `A.indicator 1` after `Nat.cast_one` / `Set.indicator_comp_of_zero`),
-- then `Finset.measurable_sum` with each term `(measurable_one.indicator hA).comp (hX i)`.
/-- The occupancy of a measurable set is a measurable real random variable. -/
theorem measurable_occupancy {N : ℕ} (X : Fin N → Ω → E) (hX : ∀ i, Measurable (X i))
    (A : Set E) (hA : MeasurableSet A) :
    Measurable (fun ω => (occupancy X A ω : ℝ)) := by
  unfold occupancy
  simp only [Nat.cast_sum]
  refine Finset.measurable_sum _ fun i _ => ?_
  have h : Measurable (fun e : E => ((A.indicator (1 : E → ℕ) e : ℕ) : ℝ)) :=
    (measurable_from_top (f := (Nat.cast : ℕ → ℝ))).comp ((measurable_one.indicator hA))
  exact h.comp (hX i)

-- SKETCH: `badEvent = ⋃ a, {ω | δ N < occupancy}`; `MeasurableSet.iUnion` and
-- `measurableSet_lt measurable_const (measurable_occupancy …)`.
/-- The bad event is measurable. -/
theorem measurableSet_badEvent {ν : Measure E} {N M : ℕ} (X : Fin N → Ω → E)
    (hX : ∀ i, Measurable (X i)) (bx : Boxes ν M) (δ : ℝ) :
    MeasurableSet (badEvent X bx δ) := by
  have : badEvent X bx δ = ⋃ a, {ω | δ * N < (occupancy X (bx.A a) ω : ℝ)} := by
    ext ω; simp [badEvent]
  rw [this]
  exact MeasurableSet.iUnion fun a =>
    measurableSet_lt measurable_const (measurable_occupancy X hX _ (bx.meas a))

-- SKETCH: Jensen for the convex `exp` (`convexOn_exp.map_integral_le`, or
-- `ConvexOn.map_integral_le` with `s = univ`) gives `exp (∫ K) ≤ ∫ exp K`; rewrite with
-- `hK0` and `Real.exp_zero`.
/-- "`A_b ≥ 1` by Jensen": for a probability measure and an integrable centered `K`,
`1 ≤ ∫ e^K`. -/
theorem one_le_integral_exp {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (K : α → ℝ) (hK : Integrable K ν) (hK0 : ∫ x, K x ∂ν = 0)
    (hexp : Integrable (fun x => Real.exp (K x)) ν) :
    1 ≤ ∫ x, Real.exp (K x) ∂ν := by
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hK hexp
  rwa [hK0, Real.exp_zero] at h

-- SKETCH: if `γ = 0` both sides are `1` (`Real.rpow_zero`, `integral_const`).  Otherwise
-- `p := b/γ ≥ 1`; `x ↦ x^p` is convex on `[0,∞)` (`convexOn_rpow`), so Jensen
-- (`ConvexOn.map_integral_le` with `s = Set.Ici 0`, a.e. membership by `Real.exp_pos`)
-- gives `(∫ exp (γ F))^p ≤ ∫ (exp (γ F))^p = ∫ exp (b F)` (`← Real.exp_mul`,
-- `Real.rpow_def_of_pos`).  Raise to the power `1/p = γ/b` with `Real.rpow_le_rpow` and
-- `Real.rpow_rpow_inv`.  Integrability of `exp (γ F)`: dominated by `1 + exp (b F)`
-- (`Integrable.mono'`, `Real.exp_le_exp`, case split on the sign of `F ω`).
-- Alternative: `eLpNorm_le_eLpNorm_of_exponent_le` for `exp F` with exponents `γ ≤ b`.
/-- Lyapunov / Hölder monotonicity: on a probability space, for `0 ≤ γ ≤ b`, `0 < b`,
`∫ e^{γ F} ≤ (∫ e^{b F})^{γ/b}`. -/
theorem integral_exp_mul_le_rpow (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : Measurable F) (b γ : ℝ) (hb : 0 < b) (hγ0 : 0 ≤ γ) (hγb : γ ≤ b)
    (hint : Integrable (fun ω => Real.exp (b * F ω)) μ) :
    ∫ ω, Real.exp (γ * F ω) ∂μ ≤ (∫ ω, Real.exp (b * F ω) ∂μ) ^ (γ / b) := by
  rcases hγ0.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hfi : Integrable (fun ω => Real.exp (γ * F ω)) μ := by
    refine Integrable.mono' ((integrable_const (1:ℝ)).add hint)
      (by fun_prop : Measurable fun ω => Real.exp (γ * F ω)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases le_total (F ω) 0 with h | h
    · have : Real.exp (γ * F ω) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have := Real.exp_pos (b * F ω)
      simp only [Pi.add_apply]; linarith
    · have : Real.exp (γ * F ω) ≤ Real.exp (b * F ω) := Real.exp_le_exp.2 (by nlinarith)
      simp only [Pi.add_apply]; linarith
  set p : ℝ := b / γ with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ hpos]; linarith
  have hpow : ∀ ω, (Real.exp (γ * F ω)) ^ p = Real.exp (b * F ω) := by
    intro ω
    rw [← Real.exp_mul]; congr 1; rw [hp]; field_simp
  have hgi : Integrable ((fun x : ℝ => x ^ p) ∘ fun ω => Real.exp (γ * F ω)) μ := by
    simpa [Function.comp_def, hpow] using hint
  have hJ := (convexOn_rpow hp1).map_integral_le (continuousOn_id.rpow_const
      (fun x _ => Or.inr (by linarith))) isClosed_Ici
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hfi hgi
  simp only [hpow] at hJ
  have h0 : 0 ≤ ∫ ω, Real.exp (γ * F ω) ∂μ := integral_nonneg fun ω => (Real.exp_pos _).le
  have := Real.rpow_le_rpow (Real.rpow_nonneg h0 p) hJ (by positivity : (0:ℝ) ≤ 1 / p)
  rw [← Real.rpow_mul h0, mul_one_div_cancel (by linarith), Real.rpow_one] at this
  have e : γ / b = 1 / p := by rw [hp]; field_simp
  rw [e]; exact this

-- SKETCH: Hölder `integral_mul_le_Lp_mul_Lq_of_nonneg hs.symm` with `f = B.indicator 1`
-- and `g = exp ∘ F` (both nonnegative; `MemLp` of the indicator from `memLp_indicator_const`
-- / `memLp_const` on a finite measure, of `exp F` from `hint` via `memLp_norm_rpow_iff` or
-- `Integrable.memLp_of_rpow`): `∫ 1_B exp F ≤ (∫ 1_B^{s'})^{1/s'} (∫ (exp F)^s)^{1/s}`.
-- Then `Set.indicator_mul_left`, `Real.one_rpow`, `integral_indicator_one hB`
-- (`= μ.real B`), and `(exp (F ω))^s = exp (s * F ω)` by `Real.exp_mul`.
/-- Hölder with an indicator (first step of eq. `eq:physical-bad-gibbs-bound` (3.3)):
`∫ 1_B e^F ≤ μ(B)^{1/s'} (∫ e^{sF})^{1/s}` for conjugate exponents `s, s'`. -/
theorem holder_indicator (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Set Ω)
    (hB : MeasurableSet B) (F : Ω → ℝ) (hF : Measurable F) (s s' : ℝ)
    (hs : s.HolderConjugate s') (hint : Integrable (fun ω => Real.exp (s * F ω)) μ) :
    ∫ ω, B.indicator (fun ω => Real.exp (F ω)) ω ∂μ
      ≤ (μ.real B) ^ (1 / s') * (∫ ω, Real.exp (s * F ω) ∂μ) ^ (1 / s) := by
  have hs0 : 0 < s := hs.pos
  have hs'0 : 0 < s' := hs.symm.pos
  have hg : MemLp (fun ω => Real.exp (F ω)) (ENNReal.ofReal s) μ := by
    rw [← integrable_norm_rpow_iff (by fun_prop) (by simpa using hs0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs0.le]
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul, mul_comm]
  have hf : MemLp (B.indicator (fun _ : Ω => (1 : ℝ))) (ENNReal.ofReal s') μ :=
    memLp_indicator_const _ hB.nullMeasurableSet _ (Or.inr (measure_ne_top _ _))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hs.symm
    (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (F ω)).le) hf hg
  have e1 : ∀ ω, B.indicator (fun _ : Ω => (1 : ℝ)) ω * Real.exp (F ω)
      = B.indicator (fun ω => Real.exp (F ω)) ω := fun ω => by
    by_cases hω : ω ∈ B <;> simp [hω]
  have e2 : ∀ ω, B.indicator (fun _ : Ω => (1 : ℝ)) ω ^ s'
      = B.indicator (fun _ : Ω => (1 : ℝ)) ω := fun ω => by
    by_cases hω : ω ∈ B <;> simp [hω, hs'0.ne']
  have e3 : ∀ ω, (Real.exp (F ω)) ^ s = Real.exp (s * F ω) := fun ω => by
    rw [← Real.exp_mul, mul_comm]
  simp only [e1, e2, e3] at h
  have e4 : ∫ ω, B.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ = μ.real B := by
    exact integral_indicator_one (μ := μ) hB
  rwa [e4] at h

/-! ### B2–B3: the rough partition-function bound and its monotonicity -/

section Rough

variable [AddGroup E] [MeasurableSub₂ E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
variable {N : ℕ} {X : Fin N → Ω → E}

-- SKETCH: `lintegral` version of `LogGas.Warmup.prod_bound_indep` (same Fubini/independence
-- computation): the integrand is nonnegative and measurable (`Real.measurable_exp`,
-- `Finset.measurable_sum`, `hK.comp ((hX_meas i).sub (hX_meas j))`), and its `lintegral` is
-- `≤ ofReal (A ^ (N-1)) < ∞` (`iIndepFun_iff_map_fun_eq_pi_map`, `lintegral_map`,
-- `measurePreserving_piFinSuccAbove`, `lintegral_prod`, `lintegral_fintype_prod`,
-- `ofReal_integral_eq_lintegral_ofReal` with `hK_int`, `hKA`).  Conclude with
-- `Integrable` = `AEStronglyMeasurable ∧ HasFiniteIntegral` and `hasFiniteIntegral_iff_ofReal`.
/-- Integrability of the one-particle Gibbs weight `exp(∑_{j≠i} K(X_i - X_j))` under the
hypotheses of eq. `eq:rough-partition-bound` (3.1). -/
theorem integrable_exp_sum (hN : 2 ≤ N) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ) (hX_law : ∀ i, μ.map (X i) = ν)
    (K : E → ℝ) (hK : Measurable K)
    (hK_int : ∀ᵐ x ∂ν, Integrable (fun y => Real.exp (K (x - y))) ν)
    (A : ℝ) (hA : 1 ≤ A) (hKA : ∀ᵐ x ∂ν, ∫ y, Real.exp (K (x - y)) ∂ν ≤ A) (i : Fin N) :
    Integrable (fun ω => Real.exp (∑ j ∈ univ.erase i, K (X i ω - X j ω))) μ := by
  sorry

-- SKETCH: `(b/2) * W g X ω = (1/N) * ∑ i, f i ω` with
-- `f i ω = (b/2) * ∑ j ∈ univ.erase i, g (X i ω - X j ω)` (`W`, `Finset.mul_sum`,
-- `mul_left_comm`).  Pointwise Jensen `convexOn_exp.map_sum_le` with weights `1/N` bounds
-- the integrand by `(1/N) ∑ i, exp (f i ω)`, which is integrable by `integrable_exp_sum`
-- (with `K := fun z => (b/2) * g z`, `Integrable.const_mul`, `integrable_finset_sum`);
-- conclude with `Integrable.mono'` (measurability: `Real.measurable_exp`, `Finset.measurable_sum`).
/-- Integrability of the Gibbs weight `exp((b/2) W_N(g))`. -/
theorem integrable_exp_W (hN : 2 ≤ N) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ) (hX_law : ∀ i, μ.map (X i) = ν)
    (g : E → ℝ) (hg : Measurable g) (b : ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hK_int : ∀ᵐ x ∂ν, Integrable (fun y => Real.exp ((b / 2) * g (x - y))) ν)
    (hKA : ∀ᵐ x ∂ν, ∫ y, Real.exp ((b / 2) * g (x - y)) ∂ν ≤ A) :
    Integrable (fun ω => Real.exp ((b / 2) * W (fun x y => g (x - y)) X ω)) μ := by
  sorry

-- SKETCH (B2): unfold `Z`, `W`; rewrite the exponent as `(1/N) * ∑ i, f i ω` as in
-- `integrable_exp_W`.  Apply `LogGas.Warmup.jensen_avg_exp` (B1; `hf_int` from
-- `integrable_exp_sum`), then bound each `∫ exp (f i)` by `A ^ (N-1)` with
-- `LogGas.Warmup.prod_bound_indep` for `K := fun z => (b/2) * g z` (`Finset.mul_sum` to
-- match `∑ j, K (X i - X j)`).  Finish with `Finset.sum_le_sum`, `Finset.sum_const`,
-- `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`, `one_div_mul_cancel` (`N ≠ 0`).
/-- Eq. `eq:rough-partition-bound` (3.1): `Z_{N,b} ≤ A_b^{N-1}`. -/
theorem rough_bound (hN : 2 ≤ N) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ) (hX_law : ∀ i, μ.map (X i) = ν)
    (g : E → ℝ) (hg : Measurable g) (b : ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hK_int : ∀ᵐ x ∂ν, Integrable (fun y => Real.exp ((b / 2) * g (x - y))) ν)
    (hKA : ∀ᵐ x ∂ν, ∫ y, Real.exp ((b / 2) * g (x - y)) ∂ν ≤ A) :
    Z μ b g X ≤ A ^ (N - 1) := by
  have hN0 : 0 < N := by omega
  set f : Fin N → Ω → ℝ := fun i ω =>
    (b / 2) * ∑ j ∈ univ.erase i, g (X i ω - X j ω) with hf
  have key : ∀ ω, (b / 2) * W (fun x y => g (x - y)) X ω = (1 / (N : ℝ)) * ∑ i, f i ω := by
    intro ω
    simp only [hf, W]
    rw [← Finset.mul_sum]
    ring
  have hfm : ∀ i, Measurable (f i) := fun i => by
    simp only [hf]
    refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact hg.comp ((hX_meas i).sub (hX_meas j))
  have hfe : ∀ i ω, f i ω = ∑ j ∈ univ.erase i, (b / 2) * g (X i ω - X j ω) := fun i ω => by
    simp only [hf]; rw [Finset.mul_sum]
  have hfi : ∀ i, Integrable (fun ω => Real.exp (f i ω)) μ := fun i => by
    simp only [hfe]
    exact integrable_exp_sum μ ν hN hX_meas hX_indep hX_law (fun z => (b / 2) * g z)
      (hg.const_mul _) hK_int A hA hKA i
  have hJ := LogGas.Warmup.jensen_avg_exp μ N hN0 f hfm hfi
  have hZ : Z μ b g X = ∫ ω, Real.exp ((1 / (N : ℝ)) * ∑ i, f i ω) ∂μ := by
    simp only [Z, key]
  rw [hZ]
  refine hJ.trans ?_
  have hb : ∀ i, ∫ ω, Real.exp (f i ω) ∂μ ≤ A ^ (N - 1) := fun i => by
    have := LogGas.Warmup.prod_bound_indep μ ν N hN X hX_meas hX_indep hX_law
      (fun z => (b / 2) * g z) (hg.const_mul _) hK_int A hA hKA i
    simpa only [hfe] using this
  calc (1 / (N : ℝ)) * ∑ i, ∫ ω, Real.exp (f i ω) ∂μ
      ≤ (1 / (N : ℝ)) * ∑ _i : Fin N, A ^ (N - 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hb i) (by positivity)
    _ = A ^ (N - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, one_div_mul_cancel (by positivity), one_mul]

-- SKETCH (B3): first inequality: `integral_exp_mul_le_rpow` with `F := W g X / 2`
-- (so `γ * F = (γ/2) * W`; `mul_div_assoc`, `mul_comm`), measurability of `W` from
-- `Finset.measurable_sum`, `hg.comp ((hX_meas i).sub (hX_meas j))`, integrability from
-- `integrable_exp_W`.  Second: `Z μ b g X ≤ A^(N-1)` by `rough_bound`, `0 ≤ Z` by
-- `integral_nonneg`, so `Z^(γ/b) ≤ (A^(N-1))^(γ/b) ≤ A^(N-1)` by `Real.rpow_le_rpow` and
-- `Real.rpow_le_rpow_of_exponent_le` / `Real.rpow_le_self_of_one_le`-style
-- (`1 ≤ A^(N-1)` from `one_le_pow₀ hA`, exponent `γ/b ≤ 1` by `div_le_one`).
/-- Hölder monotonicity after eq. `eq:rough-partition-bound` (3.1):
`Z_{N,γ} ≤ Z_{N,b}^{γ/b} ≤ A_b^{N-1}` for `0 ≤ γ ≤ b`, using `A_b ≥ 1`. -/
theorem Z_mono (hN : 2 ≤ N) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ) (hX_law : ∀ i, μ.map (X i) = ν)
    (g : E → ℝ) (hg : Measurable g) (b γ : ℝ) (hb : 0 < b) (hγ0 : 0 ≤ γ) (hγb : γ ≤ b)
    (A : ℝ) (hA : 1 ≤ A)
    (hK_int : ∀ᵐ x ∂ν, Integrable (fun y => Real.exp ((b / 2) * g (x - y))) ν)
    (hKA : ∀ᵐ x ∂ν, ∫ y, Real.exp ((b / 2) * g (x - y)) ∂ν ≤ A) :
    Z μ γ g X ≤ Z μ b g X ^ (γ / b) ∧ Z μ b g X ^ (γ / b) ≤ A ^ (N - 1) := by
  sorry

end Rough

/-! ### B4–B5: Chernoff bound and the probability of the bad event -/

section Chernoff

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
variable {N : ℕ} {X : Fin N → Ω → E}

-- SKETCH: `(occupancy X A ω : ℝ) = ∑ i, A.indicator 1 (X i ω)` (`occupancy`, `Nat.cast_sum`,
-- `Set.indicator` with `Nat.cast_one`); the summands `ω ↦ A.indicator 1 (X i ω)` are
-- independent (`hX_indep.comp` with the measurable indicator) and measurable, so
-- `ProbabilityTheory.iIndepFun.mgf_sum` factors the mgf.  Each factor is the Bernoulli mgf:
-- `∫ exp (t * 1_A (X i ω)) ∂μ = ∫ exp (t * 1_A x) ∂ν` (`integral_map` with `hX_law`) and
-- `exp (t * 1_A x) = 1 + (exp t - 1) * 1_A x` (`Set.indicator_apply`, `split_ifs`), so the
-- integral is `1 + (exp t - 1) q = 1 - q + q exp t` (`integral_add`, `integral_indicator_one`,
-- `hq`).  Finish with `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin`.
/-- The occupancy of a set of `ν`-measure `q` is `Bin(N, q)`: its mgf is
`(1 - q + q e^t)^N` (the moment generating function behind eq.
`eq:physical-bad-probability` (3.2)). -/
theorem mgf_occupancy (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = ν) (A : Set E) (hA : MeasurableSet A) (q : ℝ)
    (hq : ν.real A = q) (t : ℝ) :
    mgf (fun ω => (occupancy X A ω : ℝ)) μ t = (1 - q + q * Real.exp t) ^ N := by
  sorry

-- SKETCH (B4): `ProbabilityTheory.measure_ge_le_exp_mul_mgf (ε := δ * N)` with
-- `t := Real.log (δ * (1 - q) / (q * (1 - δ)))`, which is `≥ 0` because
-- `q (1-δ) ≤ δ (1-q)` (`Real.log_nonneg`, `one_le_div`, `nlinarith`); integrability of
-- `exp (t * occupancy)` by `Integrable.of_bound` (occupancy `≤ N`).  Insert `mgf_occupancy`:
-- `1 - q + q exp t = (1 - q)/(1 - δ)` (`Real.exp_log`, `field_simp`), so the bound is
-- `exp (-t δ N) ((1-q)/(1-δ))^N = exp (-N (δ t - log ((1-q)/(1-δ))))`
-- (`Real.exp_log`, `← Real.exp_nat_mul`, `← Real.exp_add`); finally
-- `δ t - log ((1-q)/(1-δ)) = relEnt δ q` by `Real.log_div`, `Real.log_mul` (all arguments
-- positive) and `ring`.
/-- Binomial Chernoff bound with relative-entropy exponent (used for eq.
`eq:physical-bad-probability` (3.2)): for `n_A ~ Bin(N, q)` and `q < δ < 1`,
`P(n_A ≥ δ N) ≤ exp(-N D(δ‖q))`. -/
theorem chernoff_binomial (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = ν) (A : Set E) (hA : MeasurableSet A) (q : ℝ)
    (hq : ν.real A = q) (hq0 : 0 < q) (δ : ℝ) (hqδ : q < δ) (hδ1 : δ < 1) :
    μ.real {ω | δ * N ≤ (occupancy X A ω : ℝ)} ≤ Real.exp (-(N : ℝ) * relEnt δ q) := by
  sorry

-- SKETCH (B5): `badEvent X bx δ = ⋃ a, {ω | δ N < occupancy X (bx.A a) ω}`
-- (`Set.setOf_exists`); `measureReal_iUnion_fintype_le`; each term is `≤` the `≥`-event
-- (`measureReal_mono`, `le_of_lt`), bounded by `chernoff_binomial` with `q = 1/M`
-- (`bx.real_vol`, `bx.meas`, `hM` for `0 < 1/M`); then `Finset.sum_const`,
-- `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`.
/-- Eq. `eq:physical-bad-probability` (3.2): `P(𝓑_{N,J,δ}) ≤ M exp(-N D(δ‖1/M))` for
`1/M < δ < 1`, by a union bound over the `M` boxes. -/
theorem bad_probability (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = ν) {M : ℕ} (bx : Boxes ν M) (hM : 1 ≤ M) (δ : ℝ)
    (hδM : 1 / (M : ℝ) < δ) (hδ1 : δ < 1) :
    μ.real (badEvent X bx δ) ≤ M * Real.exp (-(N : ℝ) * relEnt δ (1 / M)) := by
  sorry

end Chernoff

/-! ### B6: the Gibbs weight on the bad event -/

section Gibbs

variable [AddGroup E] [MeasurableSub₂ E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
variable {N : ℕ} {X : Fin N → Ω → E}

-- SKETCH (B6): `holder_indicator` with `B := badEvent X bx δ` (`measurableSet_badEvent`),
-- `F := (β/2) * W g X`, exponents `s, s'`; `exp (s * F) = exp (((s β)/2) * W)` so the second
-- factor is `Z μ (s β) g X ^ (1/s) ≤ (A ^ (N-1)) ^ (1/s) ≤ A ^ (N/s) = exp (N log A / s)`
-- by `Z_mono` (with `γ := s β ≤ b`, `0 ≤ s β` from `hs.pos`), `Real.rpow_le_rpow`,
-- `Real.rpow_natCast`, `Real.rpow_le_rpow_of_exponent_le hA`, `Real.rpow_def_of_pos`.
-- The first factor is `≤ (M exp (-N D))^(1/s') = M^(1/s') exp (-N D / s')` by
-- `bad_probability`, `Real.rpow_le_rpow`, `Real.mul_rpow`, `← Real.exp_mul`.
-- Combine: `Real.exp_add`, `mul_sub`, `div_eq_mul_one_div`, `mul_assoc`, `mul_comm`.
/-- Eq. `eq:physical-bad-gibbs-bound` (3.3): for conjugate exponents `s, s'` with `s β ≤ b`,
`𝔼[1_𝓑 e^{(β/2) W_N(g)}] ≤ M^{1/s'} exp{N (log A_b / s − D(δ‖1/M) / s')}`. -/
theorem bad_gibbs_bound (hN : 2 ≤ N) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ) (hX_law : ∀ i, μ.map (X i) = ν)
    {M : ℕ} (bx : Boxes ν M) (hM : 1 ≤ M)
    (g : E → ℝ) (hg : Measurable g) (b β s s' : ℝ) (hb : 0 < b) (hβ0 : 0 ≤ β)
    (hs : s.HolderConjugate s') (hβb : s * β ≤ b) (A : ℝ) (hA : 1 ≤ A)
    (hK_int : ∀ᵐ x ∂ν, Integrable (fun y => Real.exp ((b / 2) * g (x - y))) ν)
    (hKA : ∀ᵐ x ∂ν, ∫ y, Real.exp ((b / 2) * g (x - y)) ∂ν ≤ A)
    (δ : ℝ) (hδM : 1 / (M : ℝ) < δ) (hδ1 : δ < 1) :
    ∫ ω, (badEvent X bx δ).indicator
        (fun ω => Real.exp ((β / 2) * W (fun x y => g (x - y)) X ω)) ω ∂μ
      ≤ (M : ℝ) ^ (1 / s') * Real.exp (N * (Real.log A / s - relEnt δ (1 / M) / s')) := by
  sorry

end Gibbs

end LogGas.BadEvent

import Mathlib

/-!
# Phase 0 — warm-up: the rough partition-function bound, eq. (3.1)

Source: `notes/sec3-badevent.tex`, equation `eq:rough-partition-bound`:

  Z_{N,b} = E[ exp{ (1/N) Σ_i (b/2) Σ_{j≠i} g(X_i - X_j) } ]
          ≤ (1/N) Σ_i E[ exp{ (b/2) Σ_{j≠i} g(X_i - X_j) } ] = A_b^{N-1}.

The two steps are isolated here in abstract form (no torus, no kernel `g`):

* `LogGas.Warmup.jensen_avg_exp`   — the convexity step (first inequality);
* `LogGas.Warmup.prod_bound_indep` — the "integrate conditionally on `X_i`"
  step giving each summand `≤ A^{N-1}`.

Standing hypotheses H1/H2 of `notes/hypotheses.md` are not needed in this phase.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

namespace LogGas.Warmup

-- SKETCH (P0.A): Pointwise, `convexOn_exp.map_sum_le` with the equal weights
-- `w i = 1/N` (nonnegative, summing to one via `Finset.sum_const`, `card_fin`)
-- gives `exp ((1/N) * Σ f i ω) ≤ Σ (1/N) * exp (f i ω)`.  The right-hand integrand
-- is integrable by `integrable_finset_sum` and `Integrable.const_mul`; the left-hand
-- integrand is then integrable by `Integrable.mono'` (it is nonneg and dominated,
-- measurable via `Real.measurable_exp`, `Finset.measurable_sum`).  Conclude with
-- `integral_mono`, `integral_finset_sum`, `integral_const_mul`, `Finset.mul_sum`.
/-- Eq. `eq:rough-partition-bound`, first inequality (Jensen for an average of
exponents): on a probability space,
`∫ exp((1/N) Σ_i f i) dμ ≤ (1/N) Σ_i ∫ exp(f i) dμ`. -/
theorem jensen_avg_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 0 < N) (f : Fin N → Ω → ℝ)
    (hf_meas : ∀ i, Measurable (f i))
    (hf_int : ∀ i, Integrable (fun ω => Real.exp (f i ω)) μ) :
    ∫ ω, Real.exp ((1 / (N : ℝ)) * ∑ i, f i ω) ∂μ
      ≤ (1 / (N : ℝ)) * ∑ i, ∫ ω, Real.exp (f i ω) ∂μ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ ω, Real.exp ((1 / (N : ℝ)) * ∑ i, f i ω)
      ≤ ∑ i, (1 / (N : ℝ)) * Real.exp (f i ω) := by
    intro ω
    have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin N)))
      (w := fun _ => 1 / (N : ℝ)) (p := fun i => f i ω)
      (fun _ _ => by positivity)
      (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
      (fun _ _ => Set.mem_univ _)
    simpa [smul_eq_mul, ← Finset.mul_sum] using h
  have hint : Integrable (fun ω => ∑ i, (1 / (N : ℝ)) * Real.exp (f i ω)) μ :=
    integrable_finsetSum _ (fun i _ => (hf_int i).const_mul _)
  have hmeas : Measurable (fun ω => Real.exp ((1 / (N : ℝ)) * ∑ i, f i ω)) :=
    Real.measurable_exp.comp ((Finset.measurable_sum _ (fun i _ => hf_meas i)).const_mul _)
  calc ∫ ω, Real.exp ((1 / (N : ℝ)) * ∑ i, f i ω) ∂μ
      ≤ ∫ ω, ∑ i, (1 / (N : ℝ)) * Real.exp (f i ω) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
          hint (Filter.Eventually.of_forall hpt)
    _ = (1 / (N : ℝ)) * ∑ i, ∫ ω, Real.exp (f i ω) ∂μ := by
        rw [integral_finsetSum _ (fun i _ => (hf_int i).const_mul _), Finset.mul_sum]
        simp [integral_const_mul]

-- SKETCH (P0.B): Work with `lintegral` of the nonnegative integrand, so no
-- integrability is needed up front.  By `iIndepFun_iff_map_fun_eq_pi_map`
-- (using `hX_meas`, `hX_law`) the law of `ω ↦ (X · ω)` is `Measure.pi (fun _ => ν)`;
-- rewrite the integral over `μ` as one over `Measure.pi` (`lintegral_map`).  Split off
-- coordinate `i` with `measurePreserving_piFinSuccAbove` / `lintegral_prod` (Fubini) so
-- that for `ν`-a.e. `x` the inner integral is `∫⁻ ∏_{j≠i} exp(K(x - y j)) ∂pi`, which
-- factors (`lintegral_prod_eq_prod_lintegral_of_indepFun`, or `lintegral_fintype_prod`
-- on the product measure) into `∏_{j≠i} ∫⁻ exp(K(x - y)) ∂ν ≤ ofReal A ^ (N-1)`
-- (`Finset.prod_le_prod`, `Finset.prod_const`, `card_erase_of_mem`, `card_fin`); each
-- factor is `≤ ofReal A` by `hK_int`, `hKA` and `ofReal_integral_eq_lintegral_ofReal`.
-- Finally `integral_eq_lintegral_of_nonneg_ae`, `ENNReal.toReal_le_of_le_ofReal`.
/-- Eq. `eq:rough-partition-bound`, last equality (as an inequality): for i.i.d.
`X : Fin N → Ω → E` with law `ν`, a measurable `K : E → ℝ` and `A ≥ 1` with
`exp(K(x - ·))` `ν`-integrable and `∫ exp(K(x - y)) dν(y) ≤ A` for `ν`-a.e. `x`,
`∫ exp(Σ_{j ≠ i} K(X i - X j)) dμ ≤ A^(N-1)` for each `i`. -/
theorem prod_bound_indep {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [AddGroup E] [MeasurableSub₂ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (N : ℕ) (hN : 2 ≤ N) (X : Fin N → Ω → E)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = ν)
    (K : E → ℝ) (hK : Measurable K)
    (hK_int : ∀ᵐ x ∂ν, Integrable (fun y => Real.exp (K (x - y))) ν)
    (A : ℝ) (hA : 1 ≤ A)
    (hKA : ∀ᵐ x ∂ν, ∫ y, Real.exp (K (x - y)) ∂ν ≤ A)
    (i : Fin N) :
    ∫ ω, Real.exp (∑ j ∈ univ.erase i, K (X i ω - X j ω)) ∂μ ≤ A ^ (N - 1) := by
  classical
  set T : Finset (Fin N) := univ.erase i with hT
  have hiT : i ∉ T := by simp [T]
  let Z : Ω → (T → E) := fun ω j => X j ω
  have hZmeas : Measurable Z := Measurable.of_eval (fun j => hX_meas j)
  have hindZ : iIndepFun (fun (j : T) => X j) μ := hX_indep.precomp Subtype.val_injective
  have hZlaw : μ.map Z = Measure.pi (fun _ : T => ν) := by
    have := (iIndepFun_iff_map_fun_eq_pi_map (fun j : T => (hX_meas j).aemeasurable)).1 hindZ
    simpa [Z, hX_law] using this
  have hind : IndepFun (X i) Z μ := by
    have := hX_indep.indepFun_finset {i} T (by simpa using hiT) hX_meas
    have hφ : Measurable (fun f : ({i} : Finset (Fin N)) → E => f ⟨i, by simp⟩) :=
      measurable_pi_apply _
    exact this.comp hφ measurable_id
  have hW : μ.map (fun ω => (X i ω, Z ω)) = ν.prod (Measure.pi fun _ : T => ν) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hX_meas i).aemeasurable
      hZmeas.aemeasurable).1 hind, hX_law, hZlaw]
  let F : E × (T → E) → ℝ≥0∞ := fun p => ∏ j : T, ENNReal.ofReal (Real.exp (K (p.1 - p.2 j)))
  have hF : Measurable F := by
    refine Finset.measurable_prod _ (fun j _ => ?_)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (hK.comp (measurable_fst.sub (measurable_pi_apply j |>.comp measurable_snd))))
  have h1 : ∀ ω, ENNReal.ofReal (Real.exp (∑ j ∈ univ.erase i, K (X i ω - X j ω)))
      = F (X i ω, Z ω) := by
    intro ω
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    simp only [F, Z]
    exact Finset.prod_coe_sort T (fun j => ENNReal.ofReal (Real.exp (K (X i ω - X j ω)))) ▸ rfl
  have hinner : ∀ᵐ x ∂ν, ∫⁻ z, F (x, z) ∂(Measure.pi fun _ : T => ν)
      ≤ ENNReal.ofReal A ^ (N - 1) := by
    filter_upwards [hK_int, hKA] with x hx1 hx2
    have hfac : ∫⁻ z, F (x, z) ∂(Measure.pi fun _ : T => ν)
        = ∏ j : T, ∫⁻ y, ENNReal.ofReal (Real.exp (K (x - y))) ∂ν := by
      have := lintegral_prod_eq_prod_lintegral_of_indepFun (μ := Measure.pi fun _ : T => ν)
        (Finset.univ : Finset T)
        (fun (j : T) (z : T → E) => ENNReal.ofReal (Real.exp (K (x - z j))))
        (iIndepFun_pi (X := fun (_ : T) (y : E) => ENNReal.ofReal (Real.exp (K (x - y))))
          (μ := fun _ => ν) (fun _ => (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (hK.comp (measurable_const.sub measurable_id)))).aemeasurable))
        (fun j => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (hK.comp (measurable_const.sub (measurable_pi_apply j)))))
      simp only [F]
      rw [this]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact (measurePreserving_eval (fun _ : T => ν) j).lintegral_comp
        (f := fun y => ENNReal.ofReal (Real.exp (K (x - y))))
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (hK.comp (measurable_const.sub measurable_id))))
    have hle : ∫⁻ y, ENNReal.ofReal (Real.exp (K (x - y))) ∂ν ≤ ENNReal.ofReal A := by
      rw [← ofReal_integral_eq_lintegral_ofReal hx1
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
      exact ENNReal.ofReal_le_ofReal hx2
    rw [hfac]
    calc ∏ j : T, ∫⁻ y, ENNReal.ofReal (Real.exp (K (x - y))) ∂ν
        ≤ ∏ j : T, ENNReal.ofReal A := Finset.prod_le_prod (fun _ _ => hle)
      _ = ENNReal.ofReal A ^ (N - 1) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hT, Finset.card_erase_of_mem
          (mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ j ∈ univ.erase i, K (X i ω - X j ω))) ∂μ
      ≤ ENNReal.ofReal (A ^ (N - 1)) := by
    simp_rw [h1]
    have : ∫⁻ ω, F (X i ω, Z ω) ∂μ = ∫⁻ p, F p ∂(μ.map (fun ω => (X i ω, Z ω))) := by
      rw [lintegral_map hF ((hX_meas i).prodMk hZmeas)]
    rw [this, hW, lintegral_prod _ hF.aemeasurable]
    calc _ ≤ ∫⁻ x, ENNReal.ofReal A ^ (N - 1) ∂ν := lintegral_mono_ae hinner
      _ = ENNReal.ofReal (A ^ (N - 1)) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_pow (by linarith)]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (by
      refine Measurable.aestronglyMeasurable ?_
      exact Real.measurable_exp.comp (Finset.measurable_sum _ (fun j _ =>
        hK.comp ((hX_meas i).sub (hX_meas j)))))]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint

end LogGas.Warmup

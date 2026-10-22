import Mathlib

/-!
# Exponential integrability of the logarithmic singularity

Source: `notes/sec3-badevent.tex` (`A_b < ∞` for `b < 2d`), `notes/sec5-singular.tex` (5.8),
audit C6/E5.  Small-ball volume `μ(B(0,ρ)) ≤ V ρ^d` implies
`∫ exp(α max 0 log(r/|z|)) dμ < ∞` for `0 ≤ α < d`, via a dyadic shell decomposition:
`f ≤ 1 + ∑ₙ s^(n+1) 1_{B(0, 2r 2⁻ⁿ)}` with `s = 2^α`.
-/

open MeasureTheory

namespace LogGas.Physical

section
variable {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [OpensMeasurableSpace E] [Zero E]

private lemma expint_pointwise (d : ℕ) (r α : ℝ) (hr : 0 < r) (hα : 0 ≤ α) (z : E) :
    ENNReal.ofReal (Real.exp (α * max 0 (Real.log (r / dist z 0)))) ≤
      1 + ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ α) ^ (n + 1)) *
        (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)).indicator (fun _ => (1 : ENNReal)) z := by
  set x := dist z 0 with hx
  have hx0 : 0 ≤ x := dist_nonneg
  rcases hx0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  rcases le_or_gt r x with hrx | hxr
  · have : r / x ≤ 1 := (div_le_one hpos).2 hrx
    have hl : Real.log (r / x) ≤ 0 := Real.log_nonpos (by positivity) this
    rw [max_eq_left hl]; simp
  · obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one (x := x / r) (y := (1/2:ℝ))
      (by positivity) ((div_le_one hr).2 hxr.le) (by norm_num) (by norm_num)
    have hs : 0 < (2:ℝ) ^ α := by positivity
    have hmem : z ∈ Metric.ball (0 : E) (2 * r * (1 / 2) ^ n) := by
      rw [Metric.mem_ball, ← hx]
      have : x ≤ r * (1/2) ^ n := by rwa [div_le_iff₀ hr, mul_comm] at h2
      have : 0 < (1/2:ℝ) ^ n := by positivity
      nlinarith
    have hlt : r / x < 2 ^ (n + 1) := by
      have : (1/2:ℝ) ^ (n+1) * r < x := by rwa [lt_div_iff₀ hr] at h1
      rw [div_lt_iff₀ hpos]
      have e : (2:ℝ) ^ (n+1) * (1/2) ^ (n+1) = 1 := by rw [← mul_pow]; norm_num
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (n+1)]
    have hlog : max 0 (Real.log (r / x)) ≤ Real.log ((2:ℝ) ^ (n + 1)) := by
      refine max_le (by rw [Real.log_pow]; positivity) ?_
      exact Real.log_le_log (by positivity) hlt.le
    have hf : Real.exp (α * max 0 (Real.log (r / x))) ≤ ((2:ℝ) ^ α) ^ (n + 1) := by
      calc _ ≤ Real.exp (α * Real.log ((2:ℝ) ^ (n + 1))) := by gcongr
        _ = ((2:ℝ) ^ α) ^ (n + 1) := by
          rw [Real.rpow_def_of_pos two_pos, ← Real.exp_nat_mul, Real.log_pow]
          congr 1; push_cast; ring
    calc ENNReal.ofReal (Real.exp (α * max 0 (Real.log (r / x))))
        ≤ ENNReal.ofReal (((2:ℝ) ^ α) ^ (n + 1)) * 1 := by
          rw [mul_one]; exact ENNReal.ofReal_le_ofReal hf
      _ = ENNReal.ofReal (((2:ℝ) ^ α) ^ (n + 1)) *
          (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)).indicator (fun _ => (1 : ENNReal)) z := by
          rw [Set.indicator_of_mem hmem]
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ α) ^ (n + 1)) *
          (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)).indicator (fun _ => (1 : ENNReal)) z :=
          ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal (((2:ℝ) ^ α) ^ (n + 1)) *
          (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)).indicator (fun _ => (1 : ENNReal)) z) n
      _ ≤ _ := le_add_self

theorem lintegral_exp_log_sing_le (μE : Measure E) [IsProbabilityMeasure μE] (d : ℕ)
    (V r α : ℝ) (hr : 0 < r) (hα : 0 ≤ α) (hαd : α < d)
    (hball : ∀ ρ : ℝ, 0 < ρ → μE (Metric.ball (0 : E) ρ) ≤ ENNReal.ofReal (V * ρ ^ d)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫⁻ z, ENNReal.ofReal (Real.exp (α * max 0 (Real.log (r / dist z 0)))) ∂μE ≤
        ENNReal.ofReal (1 + C) := by
  set s : ℝ := (2:ℝ) ^ α with hs
  set t : ℝ := (1/2:ℝ) ^ d with ht
  set K : ℝ := max V 0 * (2 * r) ^ d with hK
  have hs0 : 0 < s := by positivity
  have ht0 : 0 < t := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hq : s * t < 1 := by
    have h1 : (2:ℝ) ^ α < (2:ℝ) ^ (d:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hαd
    rw [Real.rpow_natCast] at h1
    have e : (2:ℝ) ^ d * t = 1 := by rw [ht, ← mul_pow]; norm_num
    nlinarith
  have hq0 : 0 ≤ s * t := by positivity
  refine ⟨s * K / (1 - s * t), by have : 0 < 1 - s * t := by linarith
                                  positivity, ?_⟩
  have hterm : ∀ n : ℕ, ENNReal.ofReal (s ^ (n + 1)) *
      μE (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)) ≤ ENNReal.ofReal (s * K * (s * t) ^ n) := by
    intro n
    have hρ : 0 < 2 * r * (1 / 2:ℝ) ^ n := by positivity
    calc _ ≤ ENNReal.ofReal (s ^ (n + 1)) * ENNReal.ofReal (K * t ^ n) := by
          gcongr
          refine (hball _ hρ).trans (ENNReal.ofReal_le_ofReal ?_)
          have : V * (2 * r * (1 / 2:ℝ) ^ n) ^ d = V * (2 * r) ^ d * t ^ n := by
            rw [mul_pow, ht, ← pow_mul, ← pow_mul, mul_comm n d]; ring
          rw [this, hK]
          have : 0 ≤ (2 * r) ^ d * t ^ n := by positivity
          nlinarith [le_max_left V 0]
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; rw [mul_pow]; ring
  have hsum : Summable (fun n : ℕ => s * K * (s * t) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq).mul_left _
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (α * max 0 (Real.log (r / dist z 0)))) ∂μE
      ≤ ∫⁻ z, (1 + ∑' n : ℕ, ENNReal.ofReal (s ^ (n + 1)) *
        (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)).indicator (fun _ => (1 : ENNReal)) z) ∂μE :=
        lintegral_mono fun z => expint_pointwise d r α hr hα z
    _ = 1 + ∑' n : ℕ, ENNReal.ofReal (s ^ (n + 1)) *
          μE (Metric.ball (0 : E) (2 * r * (1 / 2) ^ n)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum]
        · congr 1
          refine tsum_congr fun n => ?_
          rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_ball)]
          congr 1
          exact lintegral_indicator_one measurableSet_ball
        · exact fun n => (measurable_const.indicator measurableSet_ball).const_mul _ |>.aemeasurable
    _ ≤ 1 + ∑' n : ℕ, ENNReal.ofReal (s * K * (s * t) ^ n) := by
        gcongr with n
        exact hterm n
    _ = ENNReal.ofReal (1 + s * K / (1 - s * t)) := by
        have hpos : 0 < 1 - s * t := by linarith
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum,
          ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
          tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
        congr 3

theorem integrable_exp_log_sing (μE : Measure E) [IsProbabilityMeasure μE] (d : ℕ)
    (V r α : ℝ) (hr : 0 < r) (hα : 0 ≤ α) (hαd : α < d)
    (hball : ∀ ρ : ℝ, 0 < ρ → μE (Metric.ball (0 : E) ρ) ≤ ENNReal.ofReal (V * ρ ^ d)) :
    Integrable (fun z => Real.exp (α * max 0 (Real.log (r / dist z 0)))) μE := by
  obtain ⟨C, -, hC⟩ := lintegral_exp_log_sing_le μE d V r α hr hα hαd hball
  have hm : Measurable (fun z : E => Real.exp (α * max 0 (Real.log (r / dist z 0)))) := by
    have hd : Measurable (fun z : E => dist z 0) :=
      (continuous_id.dist continuous_const).measurable
    exact Real.measurable_exp.comp
      (((measurable_const.max (Real.measurable_log.comp (hd.const_div r)))).const_mul α)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) (hC.trans_lt ENNReal.ofReal_lt_top)
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
end

end LogGas.Physical


import LogGas.TorusAdj
import LogGas.Singular

/-!
# PSING: the H2 singular data gives a `SingularKernel` on the torus grid

Source: `notes/sec2-cutoff.tex` (2.1), `notes/sec1-setting.tex` (1.5)-(1.6) and the
hypotheses of `notes/sec5-singular.tex`.  From a measurable, integrable `s ≥ 0` a.e., supported
a.e. in the `r`-radius ball (`r = 1/(2J)`) and bounded a.e. by `(log (r / radius))_+`, we build
the even, everywhere-defined, everywhere-supported representative `K.s` (a symmetrization of a
clamped modification `s₁` of `s`) and package it as `LogGas.Singular.SingularKernel`
with `V = 2^d`.  The theorem `singular_instance` takes the stated hypotheses; the positivity
proof of `J` is obtained from `hJ` via `by omega`.
-/

set_option autoImplicit false

open MeasureTheory LogGas.Torus

namespace LogGas.Physical

/-- The clamped modification of `s`. -/
private noncomputable def psingS1 {d : ℕ} (r : ℝ) (s : T d → ℝ) (z : T d) : ℝ :=
  if dist z 0 ≤ r ∧ 0 < dist z 0 then min (max (s z) 0) (max 0 (Real.log (r / dist z 0))) else 0

private theorem psingS1_nonneg {d : ℕ} (r : ℝ) (s : T d → ℝ) (z : T d) : 0 ≤ psingS1 r s z := by
  unfold psingS1
  split_ifs
  · exact le_min (le_max_right _ _) (le_max_left _ _)
  · exact le_rfl

private theorem psingS1_le {d : ℕ} (r : ℝ) (s : T d → ℝ) (z : T d) :
    psingS1 r s z ≤ max 0 (Real.log (r / dist z 0)) := by
  unfold psingS1
  split_ifs
  · exact min_le_right _ _
  · exact le_max_left _ _

private theorem psingS1_supp {d : ℕ} (r : ℝ) (s : T d → ℝ) (z : T d) (h : r < dist z 0) :
    psingS1 r s z = 0 := by
  unfold psingS1
  rw [if_neg]
  exact fun hh => absurd hh.1 (not_le.2 h)

private theorem psingS1_meas {d : ℕ} (r : ℝ) (s : T d → ℝ) (hs : Measurable s) :
    Measurable (psingS1 r s) := by
  have hd : Measurable fun z : T d => dist z 0 := (continuous_id.dist continuous_const).measurable
  unfold psingS1
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le hd measurable_const).inter (measurableSet_lt measurable_const hd)
  · exact (hs.max measurable_const).min
      (measurable_const.max ((measurable_const.div hd).log))

private theorem psing_dist_neg {d : ℕ} (z : T d) : dist (-z) 0 = dist z 0 := by
  simp [dist_eq_norm]

private theorem psing_singleton_null {d : ℕ} (hd : 1 ≤ d) : unif d {(0 : T d)} = 0 := by
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have hd0 : d ≠ 0 := by omega
  -- choose ρ small with 2^d ρ^d ≤ ε
  have hlim : Filter.Tendsto (fun ρ : ℝ => (2 : ℝ) ^ d * ρ ^ d) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    have : Filter.Tendsto (fun ρ : ℝ => (2 : ℝ) ^ d * ρ ^ d) (nhds 0) (nhds ((2 : ℝ) ^ d * 0 ^ d)) :=
      (continuous_const.mul (continuous_pow d)).tendsto 0
    rw [zero_pow hd0, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨ρ, hρ, hρ0⟩ := ((hlim.eventually (Iio_mem_nhds hεr)).and
    self_mem_nhdsWithin).exists
  calc unif d {(0 : T d)} ≤ unif d (Metric.ball (0 : T d) ρ) :=
        measure_mono (by intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact Metric.mem_ball_self hρ0)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ d * ρ ^ d) := ball_vol d ρ hρ0
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hρ.le
    _ = ε := ENNReal.ofReal_coe_nnreal

theorem singular_instance {d : ℕ} (hd : 1 ≤ d) (J : ℕ) (hJ : 3 ≤ J) (s : T d → ℝ)
    (hsm : Measurable s) (hsi : Integrable s (unif d)) (hs0 : ∀ᵐ x ∂unif d, 0 ≤ s x)
    (hsupp : ∀ᵐ x ∂unif d, 1 / (2 * (J : ℝ)) < radius x → s x = 0)
    (hlog : ∀ᵐ x ∂unif d, s x ≤ max 0 (Real.log ((1 / (2 * (J : ℝ))) / radius x)))
    (Cc : ℝ) (hc : ∫ z, s z ∂unif d ≤ Cc * (1 / (2 * (J : ℝ))) ^ d) :
    ∃ K : LogGas.Singular.SingularKernel (unif d) (grid d J (by omega)) (adj d J (by omega)) d
        Cc (2 ^ d),
      K.r = 1 / (2 * (J : ℝ)) ∧ K.c = ∫ z, s z ∂unif d ∧
        ∃ s₁ : T d → ℝ, s₁ =ᵐ[unif d] s ∧ ∀ z, K.s z = (s₁ z + s₁ (-z)) / 2 := by
  have hJ0 : 0 < J := by omega
  set r : ℝ := 1 / (2 * (J : ℝ)) with hr
  have hJr : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity)]; linarith
  set s₁ : T d → ℝ := psingS1 r s with hs₁
  -- a.e. equality
  have hae : s₁ =ᵐ[unif d] s := by
    have hnull : ∀ᵐ x ∂unif d, x ≠ 0 := by
      rw [ae_iff]
      simpa using psing_singleton_null hd
    filter_upwards [hs0, hsupp, hlog, hnull] with z h0 h1 h2 h3
    by_cases hz : r < dist z 0
    · have : r < radius z := lt_of_lt_of_le hz (dist_zero_le_radius z)
      rw [h1 this, hs₁, psingS1_supp r s z hz]
    · push Not at hz
      have hpos : 0 < dist z 0 := dist_pos.2 h3
      have hle : s z ≤ max 0 (Real.log (r / dist z 0)) := by
        refine h2.trans (max_le_max le_rfl ?_)
        exact Real.log_le_log (div_pos hr0 (lt_of_lt_of_le hpos (dist_zero_le_radius z)))
          (div_le_div_of_nonneg_left hr0.le hpos (dist_zero_le_radius z))
      rw [hs₁, psingS1, if_pos ⟨hz, hpos⟩, max_eq_left h0, min_eq_left hle]
  have hm1 : Measurable s₁ := psingS1_meas r s hsm
  have hi1 : Integrable s₁ (unif d) := hsi.congr hae.symm
  have hi2 : Integrable (fun z => s₁ (-z)) (unif d) := hi1.comp_neg
  have hint : ∫ z, (s₁ z + s₁ (-z)) / 2 ∂unif d = ∫ z, s z ∂unif d := by
    rw [integral_div, integral_add hi1 hi2, integral_neg_eq_self (fun z => s₁ z) (unif d),
      integral_congr_ae hae]
    ring
  refine ⟨{ s := fun z => (s₁ z + s₁ (-z)) / 2
            c := ∫ z, s z ∂unif d
            r := r
            r_pos := hr0
            r_lt_one := hr1
            V_nonneg := by positivity
            s_meas := ((hm1.add (hm1.comp measurable_neg)).div_const 2)
            s_int := (hi1.add hi2).div_const 2
            s_nonneg := fun z => by
              have := psingS1_nonneg r s z
              have := psingS1_nonneg r s (-z)
              simp only [hs₁]; linarith
            s_even := fun z => by simp [add_comm]
            s_supp := fun z hz => by
              have h2 : r < dist (-z) 0 := by rw [psing_dist_neg]; exact hz
              simp only [hs₁, psingS1_supp r s z hz, psingS1_supp r s (-z) h2]; norm_num
            s_log := Filter.Eventually.of_forall fun z => by
              have h1 := psingS1_le r s z
              have h2 := psingS1_le r s (-z)
              rw [psing_dist_neg] at h2
              simp only [hs₁]; linarith
            c_def := hint
            c_le := hc
            Mr := by
              rw [Nat.cast_pow, ← mul_pow, hr]
              apply pow_le_one₀ (by positivity)
              rw [mul_one_div, div_le_one (by positivity)]
              linarith
            ball_vol := fun ρ hρ _ => ball_vol d ρ hρ
            s_local := fun a b hab hn x hx y hy => by
              have hf := far_of_not_adj (hJ := hJ0) hab hn hx hy
              have hf' : 1 / (J : ℝ) ≤ dist (y - x) 0 := by
                have := far_of_not_adj (hJ := hJ0) hab.symm (fun h => hn h.symm) hy hx
                exact this
              have hlt : r < 1 / (J : ℝ) := by
                rw [hr, one_div_lt_one_div (by positivity) (by positivity)]; linarith
              have hneg : -(x - y) = y - x := by abel
              have h2 : r < dist (-(x - y)) 0 := by rw [hneg]; exact lt_of_lt_of_le hlt hf'
              simp only [hs₁, psingS1_supp r s _ (lt_of_lt_of_le hlt hf),
                psingS1_supp r s _ h2]; norm_num }, rfl, rfl, s₁, hae, fun z => rfl⟩

end LogGas.Physical

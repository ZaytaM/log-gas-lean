import LogGas.BadEvent

/-!
# Parameter choice for the bad-event term

Source: `notes/sec2-cutoff.tex` (parameter choice), `notes/sec3-badevent.tex`
(`eq:physical-bad-probability`), contract M3.

* `relEnt_tendsto`: `relEnt δ (1/M) → ∞` as `M → ∞`.
* `exists_conj_lt`: Hölder exponents `s, s'` with `s` as close to `1` as needed, `s * a < b`.
-/

namespace LogGas.Main

open Filter Topology

theorem relEnt_tendsto (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun M : ℕ => LogGas.BadEvent.relEnt δ (1 / (M : ℝ))) atTop atTop := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlb : Tendsto (fun M : ℕ => δ * Real.log (M : ℝ) +
      (δ * Real.log δ + (1 - δ) * Real.log (1 - δ))) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hlog.const_mul_atTop hδ0)
  refine tendsto_atTop_mono' _ ?_ hlb
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hq : 0 < 1 - 1 / (M : ℝ) := by
    have : 1 / (M : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hM'
    linarith
  have hq1 : 1 - 1 / (M : ℝ) ≤ 1 := by
    have : 0 < 1 / (M : ℝ) := by positivity
    linarith
  have hlq : Real.log (1 - 1 / (M : ℝ)) ≤ 0 := Real.log_nonpos hq.le hq1
  have h2 : Real.log ((1 - δ) / (1 - 1 / (M : ℝ))) =
      Real.log (1 - δ) - Real.log (1 - 1 / (M : ℝ)) :=
    Real.log_div (by linarith) hq.ne'
  have h3 : 0 ≤ (1 - δ) * Real.log (1 - 1 / (M : ℝ)) * (-1) := by
    nlinarith
  unfold LogGas.BadEvent.relEnt
  rw [h2]
  have h1' : Real.log (δ / (1 / (M : ℝ))) = Real.log δ + Real.log M := by
    rw [div_div_eq_mul_div, div_one, Real.log_mul hδ0.ne' hMpos.ne']
  rw [h1']
  nlinarith

theorem exists_conj_lt (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∃ s s' : ℝ, s.HolderConjugate s' ∧ s * a < b := by
  set ε : ℝ := (b - a) / (2 * (a + 1)) with hε
  have hpos : 0 < ε := div_pos (by linarith) (by linarith)
  have hs : 1 < 1 + ε := by linarith
  refine ⟨1 + ε, _, Real.HolderConjugate.conjExponent hs, ?_⟩
  have : ε * (a + 1) = (b - a) / 2 := by
    rw [hε]; field_simp
  nlinarith

end LogGas.Main

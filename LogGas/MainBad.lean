import LogGas.MainParam
import LogGas.TorusGrid

/-!
# Bad-event term of Theorem 1.1 on the torus grid

Source: `notes/sec3-badevent.tex`, eq. `eq:physical-bad-probability`; contract M3; audit B6.

`bad_term`: for `J` large, the Gibbs weight restricted to the bad event of the grid
`grid d J` is at most `(J^d)^{1/s'}`, uniformly in `N ≥ 2` and `0 ≤ β ≤ β₀`.
-/

namespace LogGas.Main

open MeasureTheory ProbabilityTheory LogGas.Torus

theorem bad_term {d : ℕ} (hd : 1 ≤ d) (g : T d → ℝ) (hg : Measurable g) (b' A : ℝ)
    (hb' : 0 < b') (hA : 1 ≤ A)
    (hK_int : ∀ x, Integrable (fun y => Real.exp ((b' / 2) * g (x - y))) (unif d))
    (hKA : ∀ x, ∫ y, Real.exp ((b' / 2) * g (x - y)) ∂unif d ≤ A)
    (s s' : ℝ) (hs : s.HolderConjugate s') (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hsβ : s * β₀ ≤ b')
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ J₁ : ℕ, ∀ (J : ℕ) (hJ : 0 < J), J₁ ≤ J → ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      ∫⁻ x, (LogGas.BadEvent.badEvent (fun i (y : Fin N → T d) => y i) (grid d J hJ) δ).indicator
          (fun x => ENNReal.ofReal (Real.exp ((β / 2) * LogGas.Spec.energy g N x))) x
          ∂(Measure.pi fun _ : Fin N => unif d)
        ≤ ENNReal.ofReal (((J ^ d : ℕ) : ℝ) ^ (1 / s')) := by
  have hs0 : 0 < s := hs.pos
  have hs'0 : 0 < s' := hs.symm.pos
  have hs1 : 1 ≤ s := by
    have h1 := hs.inv_add_inv_eq_one
    have h2 := hs.symm.inv_pos
    rw [← inv_le_one₀ hs0]
    linarith
  have hev := (relEnt_tendsto δ hδ0 hδ1).eventually_ge_atTop ((s' / s) * Real.log A)
  have hev2 := Filter.eventually_ge_atTop (⌈1 / δ⌉₊ + 1)
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 (hev.and hev2)
  refine ⟨M0, fun J hJ hJ1 N hN β hβ0 hββ₀ => ?_⟩
  have hMJ : J ≤ J ^ d := Nat.le_self_pow (by omega) J
  have hM := hM0 (J ^ d) (le_trans hJ1 hMJ)
  have hM1 : 1 ≤ J ^ d := le_trans hJ hMJ
  have hδM : 1 / ((J ^ d : ℕ) : ℝ) < δ := by
    have h1 : 1 / δ < ((J ^ d : ℕ) : ℝ) := by
      have : (⌈1 / δ⌉₊ + 1 : ℕ) ≤ J ^ d := hM.2
      have h2 := Nat.le_ceil (1 / δ)
      have h3 : ((⌈1 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ ((J ^ d : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_add, Nat.cast_one] at h3
      rw [Nat.cast_pow] at h3 ⊢
      linarith
    rw [div_lt_iff₀ (by linarith [one_div_pos.2 hδ0])]
    rw [div_lt_iff₀ hδ0] at h1
    linarith
  set X : Fin N → (Fin N → T d) → T d := fun i y => y i with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hindep : iIndepFun X (Measure.pi fun _ : Fin N => unif d) :=
    iIndepFun_pi (fun i => (measurable_id.aemeasurable))
  have hlaw : ∀ i, (Measure.pi fun _ : Fin N => unif d).map (X i) = unif d :=
    fun i => (measurePreserving_eval _ i).map_eq
  have hb := LogGas.BadEvent.bad_gibbs_bound (Measure.pi fun _ : Fin N => unif d) (unif d) hN hXm
    hindep hlaw (grid d J hJ) hM1 g hg b' β s s' hb' hβ0 hs
    (le_trans (mul_le_mul_of_nonneg_left hββ₀ hs0.le) hsβ) A hA
    (Filter.Eventually.of_forall hK_int) (Filter.Eventually.of_forall hKA) δ hδM hδ1
  have hD : (s' / s) * Real.log A ≤ LogGas.BadEvent.relEnt δ (1 / ((J ^ d : ℕ) : ℝ)) := hM.1
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hexp : Real.exp (N * (Real.log A / s
      - LogGas.BadEvent.relEnt δ (1 / ((J ^ d : ℕ) : ℝ)) / s')) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : Real.log A / s - LogGas.BadEvent.relEnt δ (1 / ((J ^ d : ℕ) : ℝ)) / s' ≤ 0 := by
      have : Real.log A / s ≤ LogGas.BadEvent.relEnt δ (1 / ((J ^ d : ℕ) : ℝ)) / s' := by
        rw [le_div_iff₀ hs'0]
        have : Real.log A / s * s' = (s' / s) * Real.log A := by field_simp
        linarith
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) this
  have hMpos : (0 : ℝ) ≤ ((J ^ d : ℕ) : ℝ) ^ (1 / s') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb2 : ∫ ω, (LogGas.BadEvent.badEvent X (grid d J hJ) δ).indicator
      (fun ω => Real.exp ((β / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω)) ω
      ∂(Measure.pi fun _ : Fin N => unif d) ≤ ((J ^ d : ℕ) : ℝ) ^ (1 / s') :=
    hb.trans (by nlinarith)
  -- integrability
  have hWm : Measurable (LogGas.BadEvent.W (fun x y => g (x - y)) X) := by
    unfold LogGas.BadEvent.W
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    exact Finset.measurable_sum _ fun j _ => hg.comp ((hXm i).sub (hXm j))
  have hint0 := LogGas.BadEvent.integrable_exp_W (Measure.pi fun _ : Fin N => unif d) (unif d) hN
    hXm hindep hlaw g hg b' A hA (Filter.Eventually.of_forall hK_int)
    (Filter.Eventually.of_forall hKA)
  have hBm := LogGas.BadEvent.measurableSet_badEvent X hXm (grid d J hJ) δ
  have hint : Integrable ((LogGas.BadEvent.badEvent X (grid d J hJ) δ).indicator
      (fun ω => Real.exp ((β / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω)))
      (Measure.pi fun _ : Fin N => unif d) := by
    refine Integrable.mono' (hint0.add (integrable_const (1 : ℝ))) ?_ ?_
    · exact ((Real.measurable_exp.comp (hWm.const_mul _)).indicator hBm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      have hle : Real.exp ((β / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω)
          ≤ Real.exp ((b' / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω) + 1 := by
        set w := LogGas.BadEvent.W (fun x y => g (x - y)) X ω
        rcases le_total 0 w with hw | hw
        · have : β / 2 * w ≤ b' / 2 * w := by
            apply mul_le_mul_of_nonneg_right _ hw
            have : β ≤ b' := by nlinarith
            linarith
          have := Real.exp_le_exp.2 this
          linarith
        · have : β / 2 * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hw
          have := Real.exp_le_one_iff.2 this
          have := Real.exp_pos (b' / 2 * w)
          linarith
      by_cases hω : ω ∈ LogGas.BadEvent.badEvent X (grid d J hJ) δ
      · rw [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hle
      · rw [Set.indicator_of_notMem hω, norm_zero]
        exact add_nonneg (Real.exp_pos _).le zero_le_one
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin N => unif d]
      (LogGas.BadEvent.badEvent X (grid d J hJ) δ).indicator
      (fun ω => Real.exp ((β / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω)) :=
    Filter.Eventually.of_forall fun ω =>
      Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) ω
  have hconv := ofReal_integral_eq_lintegral_ofReal hint hnn
  have hfun : (fun x => (LogGas.BadEvent.badEvent X (grid d J hJ) δ).indicator
        (fun x => ENNReal.ofReal (Real.exp ((β / 2) * LogGas.Spec.energy g N x))) x)
      = fun ω => ENNReal.ofReal ((LogGas.BadEvent.badEvent X (grid d J hJ) δ).indicator
      (fun ω => Real.exp ((β / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω)) ω) := by
    funext ω
    have := Set.indicator_comp_of_zero (s := LogGas.BadEvent.badEvent X (grid d J hJ) δ)
      (f := fun ω => Real.exp ((β / 2) * LogGas.BadEvent.W (fun x y => g (x - y)) X ω))
      (g := ENNReal.ofReal) ENNReal.ofReal_zero
    exact congrFun this ω
  show ∫⁻ x, (LogGas.BadEvent.badEvent X (grid d J hJ) δ).indicator
        (fun x => ENNReal.ofReal (Real.exp ((β / 2) * LogGas.Spec.energy g N x))) x ∂_ ≤ _
  rw [hfun, ← hconv]
  exact ENNReal.ofReal_le_ofReal hb2

end LogGas.Main

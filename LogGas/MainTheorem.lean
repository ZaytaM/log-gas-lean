import LogGas.MainGood
import LogGas.MainBad
import LogGas.PhysicalExp
import LogGas.SpecAE

/-!
# Theorem 1.1 (conditional form) and the principal milestone

Source: `notes/sec1-setting.tex` `thm:principal`, eq. (1.4); `notes/sec2-cutoff.tex` parameter
choice (contracts M1-M3; audit B6, D1).

* `theorem11` — under `boundedH1 g B` (H1) and the cutoff decomposition, the partition function is
  bounded uniformly in `N ≥ 2` and `β ∈ [0, β₀]`.  Constants are chosen in the order
  Hölder exponents, slice constant `A`, `δ`, `J`, all before `N` and `β`.
* `LogGas.Spec.principal` — `principalStatement`, via `boundedH1_of_logHLS`.

No deviations from the stated interface.
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus LogGas.Spec
open scoped ENNReal NNReal

namespace LogGas.Main

private theorem maintheorem_measurable_energy {d N : ℕ} (f : T d → ℝ) (hf : Measurable f) :
    Measurable (fun x : Fin N → T d => energy f N x) := by
  unfold energy
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  exact hf.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem theorem11 {d : ℕ} (hd : 2 ≤ d) (g : T d → ℝ) (hg : Measurable g) (B β₀ : ℝ)
    (hB : 0 < B) (hB2 : B ≤ 2 * d) (hβ₀ : 0 ≤ β₀) (hβB : β₀ < B)
    (hH1 : LogGas.Spec.boundedH1 g B) (hcut : LogGas.Spec.cutoff g) :
    ∃ C : ℝ≥0, ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      LogGas.Spec.partition g N β ≤ (C : ℝ≥0∞) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (0 : ℝ) < 2 * d := by have : (0 : ℝ) < d := by exact_mod_cast hd1
                                   linarith
  -- a. Hölder exponents
  obtain ⟨s, s', hs, hsβ⟩ := exists_conj_lt β₀ (2 * d) hβ₀ (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  obtain ⟨p, q, hpq, hpβ⟩ := exists_conj_lt β₀ B hβ₀ hβB
  have hs0 : 0 < s := hs.pos
  set b' : ℝ := (s * β₀ + 2 * d) / 2 with hb'
  have hsβ0 : 0 ≤ s * β₀ := mul_nonneg hs0.le hβ₀
  have hb'pos : 0 < b' := by rw [hb']; linarith
  have hsb' : s * β₀ ≤ b' := by rw [hb']; linarith
  have hb'lt : b' < 2 * d := by rw [hb']; linarith
  -- b. cutoff data
  obtain ⟨Cc, hCc, hJ⟩ := (cutoff_iff g).1 hcut
  obtain ⟨s₃, b₃, hc3⟩ := hJ 3 le_rfl
  obtain ⟨hsm, hsi, hbc, hbe, hb0, hgae, hs0', hsupp, hlog, hc0, hcle, hbpos, hspos, hdom⟩ := hc3
  have hr3 : (0 : ℝ) < 1 / (2 * ((3 : ℕ) : ℝ)) := by norm_num
  obtain ⟨A, hA1, hA⟩ := LogGas.Physical.exp_slice_bound hd1 g b₃ s₃ hg hbc
    (∫ z, s₃ z ∂unif d) (1 / (2 * ((3 : ℕ) : ℝ))) hr3 hgae hlog b' hb'pos hb'lt
  -- c. good term constants
  obtain ⟨δ₀, hδ₀, J₀, hgood⟩ := good_term hd1 g B hB hH1 β₀ hβ₀ p q hpq hpβ Cc hCc
  set δ : ℝ := min δ₀ (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  -- d. bad term
  obtain ⟨J₁, hbad⟩ := bad_term hd1 g hg b' A hb'pos hA1 (fun x => (hA x).1) (fun x => (hA x).2)
    s s' hs β₀ hβ₀ hsb' δ hδpos hδ1
  set J : ℕ := max 3 (max J₀ J₁) with hJdef
  have hJ3 : 3 ≤ J := le_max_left _ _
  have hJJ₀ : J₀ ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJJ₁ : J₁ ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨sJ, bJ, hcJ⟩ := hJ J hJ3
  obtain ⟨Cg, hCg⟩ := hgood J hJ3 hJJ₀ sJ bJ hcJ δ hδpos hδδ₀
  have hJ0 : 0 < J := by omega
  refine ⟨Real.toNNReal ((((J ^ d : ℕ) : ℝ) ^ (1 / s'))) + Real.toNNReal Cg, ?_⟩
  intro N hN β hβ hββ₀
  have hsplit := lintegral_split_compl (Measure.pi fun _ : Fin N => unif d)
    (LogGas.BadEvent.badEvent (fun i (y : Fin N → T d) => y i) (grid d J hJ0) δ)
    (LogGas.BadEvent.measurableSet_badEvent _ (fun i => measurable_pi_apply i) _ _)
    (fun x => (β / 2) * LogGas.Spec.energy g N x)
    (measurable_const.mul (maintheorem_measurable_energy g hg))
  have hgc := hCg N hN β hβ hββ₀
  rw [LogGas.Singular.goodEvent_eq_compl] at hgc
  have hbd := hbad J hJ0 hJJ₁ N hN β hβ hββ₀
  unfold LogGas.Spec.partition LogGas.Spec.weight
  rw [hsplit]
  refine (add_le_add hbd hgc).trans (le_of_eq ?_)
  rw [ENNReal.coe_add]
  rfl

end LogGas.Main

theorem LogGas.Spec.principal : LogGas.Spec.principalStatement := by
  intro d hd g B β0 hg _ _ _ hB hB2 hβ0 hβB hlog hcut
  exact LogGas.Main.theorem11 hd g hg B β0 hB hB2 hβ0 hβB (boundedH1_of_logHLS hlog) hcut

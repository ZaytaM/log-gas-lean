import LogGas.MainAE
import LogGas.PhysicalSing
import LogGas.MainBulkHyp
import LogGas.BulkTorus
import LogGas.MainHolder

/-!
# Good-event term of Theorem 1.1

Source: `notes/sec2-cutoff.tex`, eq. `eq:physical-cutoff-holder` (contracts M1, M2, PSING;
audit D1, C5, C8, C9, A9/F5).  On the good event the Gibbs weight splits, by Hölder, into the
bulk part `b_r` (Lemma 4.1) and the singular part `s̃_r` (Lemma 5.1).

* `CutoffAt` — the conjunct list of `LogGas.Spec.cutoff` at a fixed `J`; `cutoff_iff` is `Iff.rfl`.
* `good_term` — the good-event integral is bounded uniformly in `N` and `β ∈ [0, β₀]`.

No deviations from the stated interface.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LogGas.Torus LogGas.Spec

namespace LogGas.Main

def CutoffAt {d : ℕ} (g : T d → ℝ) (Cc : ℝ) (J : ℕ) (s b : T d → ℝ) : Prop :=
  Measurable s ∧ Integrable s (unif d) ∧ Continuous b ∧
      (∀ x, b (-x) = b x) ∧ (∫ x, b x ∂unif d) = 0 ∧
      (∀ᵐ x ∂unif d, g x = b x + (s x - ∫ z, s z ∂unif d)) ∧
      (∀ᵐ x ∂unif d, 0 ≤ s x) ∧
      (∀ᵐ x ∂unif d, (1 / (2 * (J : ℝ))) < radius x → s x = 0) ∧
      (∀ᵐ x ∂unif d, s x ≤ max 0 (Real.log ((1 / (2 * (J : ℝ))) / radius x))) ∧
      0 ≤ (∫ z, s z ∂unif d) ∧
      (∫ z, s z ∂unif d) ≤ Cc * (1 / (2 * (J : ℝ))) ^ d ∧
      positive b ∧ positive (fun x => s x - ∫ z, s z ∂unif d) ∧
      (∀ f : T d → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        quadratic (fun x y => b (x - y)) f ≤ quadratic (fun x y => g (x - y)) f)

theorem cutoff_iff {d : ℕ} (g : T d → ℝ) : LogGas.Spec.cutoff g ↔
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ J : ℕ, 3 ≤ J → ∃ s b : T d → ℝ, CutoffAt g Cc J s b := Iff.rfl

private theorem maingood_measurable_energy {d N : ℕ} (f : T d → ℝ) (hf : Measurable f) :
    Measurable (fun x : Fin N → T d => energy f N x) := by
  unfold energy
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  exact hf.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem good_term {d : ℕ} (hd : 1 ≤ d) (g : T d → ℝ) (B : ℝ) (hB : 0 < B)
    (hH1 : LogGas.Spec.boundedH1 g B) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (p q : ℝ)
    (hpq : p.HolderConjugate q) (hpβ : p * β₀ < B) (Cc : ℝ) (hCc : 0 ≤ Cc) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ J₀ : ℕ, ∀ (J : ℕ) (hJ : 3 ≤ J), J₀ ≤ J → ∀ s b : T d → ℝ,
      CutoffAt g Cc J s b → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ,
      0 ≤ β → β ≤ β₀ →
      ∫⁻ x, (LogGas.Singular.goodEvent (fun i (y : Fin N → T d) => y i)
          (grid d J (by omega)) δ).indicator
        (fun x => ENNReal.ofReal (Real.exp ((β / 2) * LogGas.Spec.energy g N x))) x
        ∂(Measure.pi fun _ : Fin N => unif d) ≤ ENNReal.ofReal C := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have ht0 : 0 < q * β₀ + 1 := by positivity
  obtain ⟨δ₀, r₀, hδ₀, hr₀, h51⟩ := LogGas.Singular.lemma51.{0, 0} (μE := unif d) d hd Cc (2 ^ d)
    (q * β₀ + 1) ht0
  refine ⟨δ₀, hδ₀, ⌈1 / (2 * r₀)⌉₊, ?_⟩
  intro J hJ hJ₀ s b hcut δ hδ hδδ₀
  obtain ⟨hsm, hsi, hbc, hbe, hb0, hgae, hs0, hsupp, hlog, hc0, hcle, hbpos, hspos, hdom⟩ := hcut
  have hJ0 : 0 < J := by omega
  have hr : 1 / (2 * (J : ℝ)) ≤ r₀ := by
    have h1 : 1 / (2 * r₀) ≤ (J : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hJ₀)
    have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ0
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨K, hKr, hKc, s₁, hs₁, hKs⟩ := LogGas.Physical.singular_instance hd J hJ s hsm hsi hs0
    hsupp hlog Cc hcle
  -- bulk constant
  obtain ⟨CK, hCK⟩ := bulk_hypothesis hB hH1 hbc hbe hb0 hbpos hdom
  obtain ⟨Cb, hCb0, hCb⟩ := LogGas.Bulk.lemma41 hCK
    (fun κ hκ => by
      obtain ⟨J', hJ', h⟩ := rJ_small (fun x y => b (x - y))
        (hbc.comp (continuous_fst.sub continuous_snd)) κ hκ
      exact ⟨J' ^ d, grid d J' hJ', h⟩) (p * β₀) (by positivity) hpβ
  set M : ℕ := J ^ d with hM
  refine ⟨Cb ^ (1 / p) * ((8 / 3 : ℝ) ^ (((M : ℝ) + 1) / 2)) ^ (1 / q), ?_⟩
  intro N hN β hβ hββ₀
  have hN1 : 1 ≤ N := by omega
  set μ : Measure (Fin N → T d) := Measure.pi fun _ : Fin N => unif d with hμ
  set X : Fin N → (Fin N → T d) → T d := fun i y => y i with hX
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hXi : iIndepFun X μ := iIndepFun_pi (μ := fun _ : Fin N => unif d) (X := fun _ => id)
    (fun i => aemeasurable_id)
  have hXl : ∀ i, μ.map (X i) = unif d := fun i =>
    (measurePreserving_eval (fun _ : Fin N => unif d) i).map_eq
  set A := LogGas.Singular.goodEvent X (grid d J hJ0) δ with hA
  have hAm : MeasurableSet A := LogGas.Singular.measurableSet_goodEvent X hXm _ δ
  -- a.e. decomposition of the energy
  have hgae' : g =ᵐ[unif d] fun z => b z + (s₁ z - K.c) := by
    filter_upwards [hgae, hs₁] with z hz hz1
    rw [hz, hz1, hKc]
  have hstil : ∀ z, K.stilde z = (s₁ z + s₁ (-z)) / 2 - K.c := fun z => by
    unfold LogGas.Singular.SingularKernel.stilde; rw [hKs z]
  have hE : ∀ᵐ x ∂μ, energy g N x = energy b N x + energy K.stilde N x := by
    filter_upwards [ae_energy_congr (N := N) hgae'] with x hx
    rw [hx, energy_add, energy_congr_sym K.stilde s₁ K.c hstil]
  have hbm : Measurable b := hbc.measurable
  have hstm : Measurable K.stilde := K.s_meas.sub measurable_const
  have hF : Measurable fun x : Fin N → T d => (β / 2) * energy b N x :=
    measurable_const.mul (maingood_measurable_energy b hbm)
  have hG : Measurable fun x : Fin N → T d => (β / 2) * energy K.stilde N x :=
    measurable_const.mul (maingood_measurable_energy _ hstm)
  have hcongr : ∫⁻ x, A.indicator
        (fun x => ENNReal.ofReal (Real.exp ((β / 2) * energy g N x))) x ∂μ
      = ∫⁻ x, A.indicator (fun x => ENNReal.ofReal (Real.exp
          ((β / 2) * energy b N x + (β / 2) * energy K.stilde N x))) x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hE] with x hx
    by_cases hxA : x ∈ A
    · simp only [Set.indicator_of_mem hxA, hx]; congr 3; ring
    · simp [Set.indicator_of_notMem hxA]
  refine hcongr.le.trans ((holder_split μ A hAm _ _ hF hG p q hpq).trans ?_)
  -- bulk factor
  have hβp : 0 ≤ p * β := by positivity
  have hpβle : p * β ≤ p * β₀ := mul_le_mul_of_nonneg_left hββ₀ hp0.le
  obtain ⟨hint1, hbd1⟩ := hCb μ hN1 X hXm hXi hXl (p * β) hβp hpβle
  have e1 : ∀ x : Fin N → T d, p * ((β / 2) * energy b N x)
      = (p * β / 2) * LogGas.BadEvent.W (fun u v => b (u - v)) X x := fun x => by
    show _ = (p * β / 2) * energy b N x
    ring
  have h1 : ∫⁻ x, ENNReal.ofReal (Real.exp (p * ((β / 2) * energy b N x))) ∂μ
      ≤ ENNReal.ofReal Cb := by
    simp only [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hbd1
  -- singular factor
  have hqβ : 0 ≤ q * β := by positivity
  have hqβle : q * β ≤ q * β₀ + 1 := by
    have := mul_le_mul_of_nonneg_left hββ₀ hq0.le
    linarith
  obtain ⟨hint2, hbd2⟩ := h51 (grid d J hJ0) (adj d J hJ0) (fun a => degree_adj_le a) K
    (by rw [hKr]; exact hr) δ hδ hδδ₀ μ hN1 X hXm hXi hXl (q * β) hqβ hqβle
  have e2 : ∀ x : Fin N → T d, q * ((β / 2) * energy K.stilde N x)
      = (q * β / 2) * LogGas.BadEvent.W (fun u v => K.stilde (u - v)) X x := fun x => by
    show _ = (q * β / 2) * energy K.stilde N x
    ring
  have h2 : ∫⁻ x, A.indicator
        (fun x => ENNReal.ofReal (Real.exp (q * ((β / 2) * energy K.stilde N x)))) x ∂μ
      ≤ ENNReal.ofReal ((8 / 3 : ℝ) ^ (((M : ℝ) + 1) / 2)) := by
    have hpt : ∀ x, A.indicator
        (fun x => ENNReal.ofReal (Real.exp (q * ((β / 2) * energy K.stilde N x)))) x
        = ENNReal.ofReal (A.indicator (fun x => Real.exp ((q * β / 2) *
            LogGas.BadEvent.W (fun u v => K.stilde (u - v)) X x)) x) := fun x => by
      by_cases hxA : x ∈ A
      · simp only [Set.indicator_of_mem hxA, e2]
      · simp [Set.indicator_of_notMem hxA]
    simp only [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun x =>
      Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) x)]
    exact ENNReal.ofReal_le_ofReal hbd2
  have h8 : (0 : ℝ) ≤ (8 / 3 : ℝ) ^ (((M : ℝ) + 1) / 2) := by positivity
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hCb0 _),
    ← ENNReal.ofReal_rpow_of_nonneg hCb0 (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg h8 (by positivity)]
  exact mul_le_mul' (ENNReal.rpow_le_rpow h1 (by positivity))
    (ENNReal.rpow_le_rpow h2 (by positivity))

end LogGas.Main

import LogGas.MainAE
import LogGas.PhysicalSing

/-!
# Singular factor of the good-event Hölder split

Source: `notes/sec5-singular.tex` Lemma 5.1 on the concrete torus grid, and
`notes/sec2-cutoff.tex` eq. `eq:physical-cutoff-holder`; contracts PSING; audit A4, A9, F5, C5, D1.

`sing_factor`: for `J` large and `δ` small, `E[1_{good} exp((t/2) W_N(s - ∫s))] ≤ (8/3)^{(J^d+1)/2}`
in lintegral form for `Spec.energy`, uniformly in `N ≥ 1` and `0 ≤ t ≤ t₀`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory LogGas.Torus LogGas.Spec

namespace LogGas.Main

theorem sing_factor {d : ℕ} (hd : 1 ≤ d) (Cc t0 : ℝ) (ht0 : 0 < t0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ J₀ : ℕ, ∀ (J : ℕ) (hJ : 3 ≤ J), J₀ ≤ J → ∀ s : T d → ℝ, Measurable s →
      Integrable s (unif d) → (∀ᵐ x ∂unif d, 0 ≤ s x) →
      (∀ᵐ x ∂unif d, (1 / (2 * (J : ℝ))) < radius x → s x = 0) →
      (∀ᵐ x ∂unif d, s x ≤ max 0 (Real.log ((1 / (2 * (J : ℝ))) / radius x))) →
      (∫ z, s z ∂unif d) ≤ Cc * (1 / (2 * (J : ℝ))) ^ d →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ t0 →
      ∫⁻ x, (LogGas.Singular.goodEvent (fun i (y : Fin N → T d) => y i) (grid d J (by omega)) δ).indicator
          (fun x => ENNReal.ofReal (Real.exp ((t / 2) *
            LogGas.Spec.energy (fun z => s z - ∫ w, s w ∂unif d) N x))) x
          ∂(Measure.pi fun _ : Fin N => unif d)
        ≤ ENNReal.ofReal ((8 / 3 : ℝ) ^ ((((J ^ d : ℕ) : ℝ) + 1) / 2)) := by
  obtain ⟨δ0, r0, hδ0, hr0, H⟩ :=
    LogGas.Singular.lemma51 (μE := unif d) d hd Cc (2 ^ d) t0 ht0
  refine ⟨δ0, hδ0, ⌈1 / (2 * r0)⌉₊ + 1, ?_⟩
  intro J hJ hJ0 s hsm hsi hs0 hsupp hlog hc δ hδ hδδ N hN t ht htt
  have hJpos : (0 : ℝ) < J := by
    have : (3 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hr : 1 / (2 * (J : ℝ)) ≤ r0 := by
    have h1 : ((⌈1 / (2 * r0)⌉₊ + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hJ0
    have h2 := Nat.le_ceil (1 / (2 * r0))
    rw [Nat.cast_add, Nat.cast_one] at h1
    have h3 : 1 / (2 * r0) < J := by linarith
    rw [div_lt_iff₀ (by positivity)] at h3
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨K, hKr, hKc, s1, hs1, hKs⟩ :=
    LogGas.Physical.singular_instance hd J hJ s hsm hsi hs0 hsupp hlog Cc hc
  set X : Fin N → (Fin N → T d) → T d := fun i y => y i with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hindep : iIndepFun X (Measure.pi fun _ : Fin N => unif d) :=
    iIndepFun_pi (fun i => (measurable_id.aemeasurable))
  have hlaw : ∀ i, (Measure.pi fun _ : Fin N => unif d).map (X i) = unif d :=
    fun i => (measurePreserving_eval _ i).map_eq
  have hmain := H (grid d J (by omega)) (adj d J (by omega))
    (fun a => degree_adj_le a) K (hKr ▸ hr) δ hδ hδδ
    (Measure.pi fun _ : Fin N => unif d) hN X hXm hindep hlaw t ht htt
  set A := LogGas.Singular.goodEvent X (grid d J (by omega)) δ with hA
  have hKe : ∀ x : Fin N → T d, LogGas.BadEvent.W (fun u v => K.stilde (u - v)) X x =
      energy (fun z => s1 z - ∫ w, s w ∂unif d) N x := by
    intro x
    rw [← energy_eq_W]
    refine energy_congr_sym _ s1 (∫ w, s w ∂unif d) (fun z => ?_) x
    unfold LogGas.Singular.SingularKernel.stilde
    rw [hKs z, hKc]
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => unif d),
      energy (fun z => s z - ∫ w, s w ∂unif d) N x =
        energy (fun z => s1 z - ∫ w, s w ∂unif d) N x := by
    have : (fun z => s z - ∫ w, s w ∂unif d) =ᵐ[unif d]
        (fun z => s1 z - ∫ w, s w ∂unif d) := by
      filter_upwards [hs1] with z hz
      rw [hz]
    exact ae_energy_congr this
  have hconv : ∫⁻ x, A.indicator
      (fun x => ENNReal.ofReal (Real.exp ((t / 2) *
        energy (fun z => s z - ∫ w, s w ∂unif d) N x))) x
        ∂(Measure.pi fun _ : Fin N => unif d) =
      ∫⁻ x, ENNReal.ofReal (A.indicator
        (fun x => Real.exp ((t / 2) * LogGas.BadEvent.W (fun u v => K.stilde (u - v)) X x)) x)
        ∂(Measure.pi fun _ : Fin N => unif d) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA, hKe, hx]
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, ENNReal.ofReal_zero]
  rw [hconv, ← ofReal_integral_eq_lintegral_ofReal hmain.1
    (Filter.Eventually.of_forall fun x => Set.indicator_nonneg
      (fun _ _ => (Real.exp_pos _).le) x)]
  exact ENNReal.ofReal_le_ofReal (by
    simpa [Nat.cast_pow] using hmain.2)

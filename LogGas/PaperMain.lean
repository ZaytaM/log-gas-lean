import LogGas.MainTheorem
import LogGas.CutoffMain
import LogGas.FourierUnique
import LogGas.KernelExists

/-!
# Paper Theorem 1.1 for the normalized kernel

Source: `PaperChallenge.lean` (`PaperTheorem`, `LogKernelExists`), equations (1.1)–(1.4).
The constant `C` is chosen (depending only on `d, B, β₀`) before the kernel representative `g`;
this holds because any two `IsLogKernel` representatives agree a.e. (`ae_eq_of_coeff_eq`) and the
partition function is a.e.-invariant (`partition_congr_ae`).
-/

namespace LogGas.Paper
open MeasureTheory LogGas.Torus LogGas.Spec LogGas.Fourier
open scoped ENNReal NNReal

def paperTheorem : Prop := ∀ d : ℕ, 2 ≤ d → ∀ B : ℝ, 0 < B → B ≤ 2 * d → ∀ β₀ : ℝ, 0 ≤ β₀ →
  β₀ < B → ∃ C : ℝ≥0, ∀ g : T d → ℝ, IsLogKernel d g → LogGas.Spec.paperLogHLS g B →
    ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → LogGas.Spec.partition g N β ≤ (C : ℝ≥0∞)

def logKernelExists : Prop := ∀ d : ℕ, 2 ≤ d → ∃ g : T d → ℝ, IsLogKernel d g

theorem paper_main : paperTheorem := by
  classical
  intro d hd B hB hB2 β₀ hβ₀ hβB
  by_cases h : ∃ g₀, IsLogKernel d g₀ ∧ LogGas.Spec.paperLogHLS g₀ B
  · obtain ⟨g₀, hk₀, hH₀⟩ := h
    have hH1 := boundedH1_of_paperLogHLS hk₀.2.1 hH₀
    have hcut := LogGas.Cutoff.cutoff_of_isLogKernel hd hk₀
    obtain ⟨C, hC⟩ := LogGas.Main.theorem11 hd g₀ hk₀.1 B β₀ hB hB2 hβ₀ hβB hH1 hcut
    refine ⟨C, fun g hg _ N hN β hβ hββ => ?_⟩
    have hae : g =ᵐ[unif d] g₀ :=
      ae_eq_of_coeff_eq g g₀ hg.2.1 hk₀.2.1 fun k => by rw [hg.2.2 k, hk₀.2.2 k]
    rw [partition_congr_ae hae]
    exact hC N hN β hβ hββ
  · exact ⟨0, fun g hg hH => absurd ⟨g, hg, hH⟩ h⟩

theorem kernel_exists : logKernelExists := fun d hd => LogGas.Fourier.kernel_exists d hd

end LogGas.Paper

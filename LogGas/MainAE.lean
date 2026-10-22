import LogGas.SpecAE
import LogGas.BadEvent

/-!
# Pointwise and a.e. identities for the torus energy

Source: `notes/sec2-cutoff.tex` (eq. `eq:physical-cutoff-holder`); audit items A9, F5, D1.
Identifies `Spec.energy` with `BadEvent.W`, shows additivity, invariance under `z ↦ -z`,
the symmetrization identity `energy_congr_sym`, and a.e.-invariance under a.e. change of `g`.
-/

set_option autoImplicit false
open MeasureTheory LogGas.Torus LogGas.Spec
open scoped BigOperators

namespace LogGas.Main

theorem energy_eq_W {d N : ℕ} (g : T d → ℝ) (x : Fin N → T d) :
    LogGas.Spec.energy g N x =
      LogGas.BadEvent.W (fun u v => g (u - v)) (fun i (y : Fin N → T d) => y i) x := rfl

theorem energy_add {d N : ℕ} (f h : T d → ℝ) (x : Fin N → T d) :
    energy (fun z => f z + h z) N x = energy f N x + energy h N x := by
  unfold energy
  simp only [Finset.sum_add_distrib, mul_add]

private theorem mainae_energy_smul {d N : ℕ} (f : T d → ℝ) (a : ℝ) (x : Fin N → T d) :
    energy (fun z => a * f z) N x = a * energy f N x := by
  unfold energy
  simp only [← Finset.mul_sum]
  ring

theorem energy_neg {d N : ℕ} (f : T d → ℝ) (x : Fin N → T d) :
    energy (fun z => f (-z)) N x = energy f N x := by
  unfold energy
  congr 1
  have h1 : ∀ (F : Fin N → Fin N → ℝ),
      ∑ i, ∑ j ∈ Finset.univ.erase i, F i j = ∑ i, ∑ j, F i j - ∑ i, F i i := by
    intro F
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_erase_eq_sub (Finset.mem_univ i)
  rw [h1 (fun i j => f (-(x i - x j))), h1 (fun i j => f (x i - x j))]
  have : ∑ i, ∑ j, f (-(x i - x j)) = ∑ i, ∑ j, f (x i - x j) := by
    rw [Finset.sum_comm]
    simp only [neg_sub]
  rw [this]
  simp

private theorem mainae_energy_sub_const {d N : ℕ} (f : T d → ℝ) (c : ℝ) (x : Fin N → T d) :
    energy (fun z => f z - c) N x = energy f N x - c * energy (fun _ => (1 : ℝ)) N x := by
  have h1 := energy_add (N := N) f (fun _ => (-1 : ℝ) * c) x
  have h2 := mainae_energy_smul (N := N) (fun _ : T d => (1 : ℝ)) (-c) x
  have h3 : (fun z : T d => f z - c) = fun z => f z + (-1 : ℝ) * c := by
    funext z; ring
  have h4 : (fun _ : T d => (-1 : ℝ) * c) = fun _ => (-c) * 1 := by
    funext z; ring
  rw [h3, h1, h4, h2]
  ring

theorem energy_congr_sym {d N : ℕ} (f f₁ : T d → ℝ) (c : ℝ)
    (h : ∀ z, f z = (f₁ z + f₁ (-z)) / 2 - c) (x : Fin N → T d) :
    energy f N x = energy (fun z => f₁ z - c) N x := by
  have hf : f = fun z => (1 / 2 : ℝ) * (f₁ z + f₁ (-z)) - c := by
    funext z; rw [h z]; ring
  rw [hf, mainae_energy_sub_const, mainae_energy_sub_const (fun z => f₁ z),
    mainae_energy_smul (fun z => f₁ z + f₁ (-z)) (1 / 2), energy_add f₁ (fun z => f₁ (-z)),
    energy_neg]
  ring

theorem ae_energy_congr {d N : ℕ} {g g' : T d → ℝ} (h : g =ᵐ[unif d] g') :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin N => unif d), energy g N x = energy g' N x := by
  have hall : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => unif d),
      ∀ i j : Fin N, i ≠ j → g (x i - x j) = g' (x i - x j) := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun x hne => absurd hij hne
    · filter_upwards [ae_pair_sub (P := fun z => g z = g' z) h i j hij] with x hx _ using hx
  filter_upwards [hall] with x hx
  unfold energy
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact hx i j (Finset.ne_of_mem_erase hj).symm

end LogGas.Main

import LogGas.TorusGrid

/-!
# Periodic box adjacency on the torus

Periodic adjacency of the boxes of `grid d J hJ` (`notes/sec1-setting.tex`, after eq. (1.6),
`eq:physical-neighbor-events`; audit A6, C5): two distinct boxes are adjacent iff in every
coordinate their cyclic index distance in `ℤ/J` is `≤ 1`.  The cyclic closeness of indices
`p q < J` is encoded without `%` as `p = q ∨ p + 1 = q ∨ q + 1 = p ∨ (p = J-1 ∧ q = 0) ∨
(q = J-1 ∧ p = 0)`.  Non-adjacent distinct boxes are `1/J`-separated in the sup metric.
-/

set_option autoImplicit false

namespace LogGas.Torus

/-- Cyclic closeness (distance `≤ 1` in `ℤ/J`) of two indices. -/
def adjClose (J p q : ℕ) : Prop :=
  p = q ∨ p + 1 = q ∨ q + 1 = p ∨ (p + 1 = J ∧ q = 0) ∨ (q + 1 = J ∧ p = 0)

instance (J p q : ℕ) : Decidable (adjClose J p q) := by unfold adjClose; infer_instance

/-- Periodic box adjacency. -/
def adj (d J : ℕ) (_hJ : 0 < J) : SimpleGraph (Fin (J ^ d)) where
  Adj a b := a ≠ b ∧ ∀ i, adjClose J (finFunctionFinEquiv.symm a i) (finFunctionFinEquiv.symm b i)
  symm := ⟨fun a b ⟨h, h2⟩ => by
    refine ⟨h.symm, fun i => ?_⟩
    have := h2 i
    unfold adjClose at *
    omega⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (d J : ℕ) (hJ : 0 < J) : DecidableRel (adj d J hJ).Adj := fun a b => by
  unfold adj; simp only; infer_instance

private def adjOff (J p q : ℕ) : Fin 3 :=
  if p = q then 0 else if (p + 1 = q ∨ (p + 1 = J ∧ q = 0)) then 1 else 2

private theorem adjOff_inj {J p q q' : ℕ} (hq : q < J) (hq' : q' < J) (hp : p < J)
    (h : adjClose J p q) (h' : adjClose J p q') (he : adjOff J p q = adjOff J p q') : q = q' := by
  unfold adjClose at h h'
  unfold adjOff at he
  split_ifs at he <;> omega

theorem degree_adj_le {d J : ℕ} {hJ : 0 < J} (a : Fin (J ^ d)) :
    (adj d J hJ).degree a ≤ 3 ^ d - 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let f : Fin (J ^ d) → (Fin d → Fin 3) := fun b i =>
    adjOff J (finFunctionFinEquiv.symm a i) (finFunctionFinEquiv.symm b i)
  have hcard : ((Finset.univ : Finset (Fin d → Fin 3)).erase 0).card = 3 ^ d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    have hb' : (adj d J hJ).Adj a b := by simpa using hb
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
      Set.mem_singleton_iff, true_and]
    intro h0
    apply hb'.1
    apply finFunctionFinEquiv.symm.injective
    funext i
    have := congrFun h0 i
    simp only [f, adjOff, Pi.zero_apply] at this
    split_ifs at this with h1
    · exact Fin.ext h1
    · exact absurd this (by decide)
    · exact absurd this (by decide)
  · intro b hb b' hb' he
    have h1 : (adj d J hJ).Adj a b := by simpa using hb
    have h2 : (adj d J hJ).Adj a b' := by simpa using hb'
    apply finFunctionFinEquiv.symm.injective
    funext i
    exact Fin.ext (adjOff_inj (finFunctionFinEquiv.symm b i).2 (finFunctionFinEquiv.symm b' i).2
      (finFunctionFinEquiv.symm a i).2 (h1.2 i) (h2.2 i) (congrFun he i))

private theorem adjFar_mem {J : ℕ} (hJ : 0 < J) (t : AddCircle (1 : ℝ)) :
    gridRep t ∈ Set.Ioc ((gridIdx J hJ t : ℕ) / (J : ℝ)) (((gridIdx J hJ t : ℕ) + 1) / (J : ℝ)) := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have hm : gridRep t ∈ Set.Ioc (0 : ℝ) 1 := by
    have := (AddCircle.equivIoc 1 0 t).2
    simpa [gridRep] using this
  have hpos : 0 < (J : ℝ) * gridRep t := mul_pos hJ' hm.1
  have hc : 1 ≤ ⌈(J : ℝ) * gridRep t⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have e : ((gridIdx J hJ t : ℕ) : ℝ) + 1 = ⌈(J : ℝ) * gridRep t⌉₊ := by
    have : (gridIdx J hJ t : ℕ) + 1 = ⌈(J : ℝ) * gridRep t⌉₊ := by
      simp only [gridIdx]; omega
    exact_mod_cast this
  have h1 := Nat.ceil_lt_add_one hpos.le
  have h2 := Nat.le_ceil ((J : ℝ) * gridRep t)
  constructor
  · rw [div_lt_iff₀ hJ']; nlinarith
  · rw [le_div_iff₀ hJ']; nlinarith

private theorem adjFar_coord {J : ℕ} (hJ : 0 < J) {s t : AddCircle (1 : ℝ)}
    (h : ¬ adjClose J (gridIdx J hJ s) (gridIdx J hJ t)) : 1 / (J : ℝ) ≤ dist s t := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have hs : (gridRep s : AddCircle (1 : ℝ)) = s := by simp [gridRep]
  have ht : (gridRep t : AddCircle (1 : ℝ)) = t := by simp [gridRep]
  have h1 := adjFar_mem hJ s
  have h2 := adjFar_mem hJ t
  have hp := (gridIdx J hJ s).2
  have hq := (gridIdx J hJ t).2
  generalize (gridIdx J hJ s : ℕ) = p at *
  generalize (gridIdx J hJ t : ℕ) = q at *
  rw [← hs, ← ht, dist_eq_norm, ← QuotientAddGroup.mk_sub]
  have : ‖(((gridRep s - gridRep t : ℝ)) : AddCircle (1 : ℝ))‖ =
      |(gridRep s - gridRep t) - (round (gridRep s - gridRep t) : ℝ)| := by
    rw [AddCircle.norm_eq]; simp
  rw [this]
  set n := round (gridRep s - gridRep t) with hn
  have hcl : ¬ ((p : ℤ) - q - n * J = 0 ∨ (p : ℤ) - q - n * J = 1 ∨ (p : ℤ) - q - n * J = -1) := by
    intro hc
    apply h
    unfold adjClose
    have hn3 : n = 0 ∨ n * (J : ℤ) ≥ J ∨ n * (J : ℤ) ≤ -(J : ℤ) := by
      rcases lt_trichotomy n 0 with h0 | h0 | h0
      · right; right; nlinarith
      · left; exact h0
      · right; left; nlinarith
    rcases hn3 with h3 | h3 | h3
    · rw [h3] at hc; omega
    · omega
    · omega
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  rw [div_lt_iff₀ hJ'] at a1
  rw [le_div_iff₀ hJ'] at a2
  rw [div_lt_iff₀ hJ'] at b1
  rw [le_div_iff₀ hJ'] at b2
  have hm : (p : ℤ) - q - n * J ≥ 2 ∨ (p : ℤ) - q - n * J ≤ -2 := by omega
  rw [le_abs]
  rcases hm with hm | hm
  · left
    have : ((p : ℤ) - q - n * J : ℤ) ≥ 2 := hm
    have h4 : ((p : ℝ) - q - n * J) ≥ 2 := by exact_mod_cast this
    rw [div_le_iff₀ hJ']
    nlinarith
  · right
    have h4 : ((p : ℝ) - q - n * J) ≤ -2 := by exact_mod_cast hm
    rw [div_le_iff₀ hJ']
    nlinarith

theorem far_of_not_adj {d J : ℕ} {hJ : 0 < J} {a b : Fin (J ^ d)} (hab : a ≠ b)
    (hn : ¬ (adj d J hJ).Adj a b) {x y : T d} (hx : x ∈ (grid d J hJ).A a)
    (hy : y ∈ (grid d J hJ).A b) : 1 / (J : ℝ) ≤ dist (x - y) 0 := by
  have : ∃ i, ¬ adjClose J (finFunctionFinEquiv.symm a i) (finFunctionFinEquiv.symm b i) := by
    by_contra hc
    push Not at hc
    exact hn ⟨hab, hc⟩
  obtain ⟨i, hi⟩ := this
  have hx' : gridIdx J hJ (x i) = finFunctionFinEquiv.symm a i := congrFun (mem_grid_iff.1 hx) i
  have hy' : gridIdx J hJ (y i) = finFunctionFinEquiv.symm b i := congrFun (mem_grid_iff.1 hy) i
  rw [← hx', ← hy'] at hi
  have h1 := adjFar_coord hJ hi
  refine h1.trans ?_
  have := dist_le_pi_dist (x - y) 0 i
  simpa [dist_eq_norm] using this

end LogGas.Torus

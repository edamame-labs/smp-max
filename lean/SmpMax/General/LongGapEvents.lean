import SmpMax.General.RelativeOrderProbability
import SmpMax.General.FiniteAverageAlgebra
import Mathlib.Tactic.IntervalCases

/-!
# Longer opposite-side events around a padded pivot

Forty-nine distinct labels represent the pivot and twenty-four positions
on each side. Events use at most three cut-side positions and up to
twenty-three opposite-side positions before the stopping label.
-/

namespace SmpMax.General.LongGap

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open FiniteProbability PermutationCounting

variable {N : ℕ}

def afterIndices (j k : ℕ) : Finset (Fin 49) :=
  Finset.univ.filter (fun i => (1 ≤ i.val ∧ i.val ≤ k) ∨ (25 ≤ i.val ∧ i.val < 25 + j))

def boundary (j : ℕ) (hj : j ≤ 23) : Fin 49 := ⟨j + 25, by omega⟩

@[simp] theorem boundary_zero : boundary 0 (by decide) = (25 : Fin 49) := by decide
@[simp] theorem boundary_one : boundary 1 (by decide) = (26 : Fin 49) := by decide
@[simp] theorem boundary_two : boundary 2 (by decide) = (27 : Fin 49) := by decide

def afterLabels (f : Fin 49 → Fin N) (j k : ℕ) : Finset (Fin N) :=
  (afterIndices j k).image f

theorem afterIndices_card {j k : ℕ} (hj : j ≤ 23) (hk : k ≤ 3) :
    (afterIndices j k).card = j + k := by
  interval_cases j <;> interval_cases k <;> decide

theorem afterLabels_card (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    {j k : ℕ} (hj : j ≤ 23) (hk : k ≤ 3) : (afterLabels f j k).card = j + k := by
  rw [afterLabels, Finset.card_image_of_injective _ hinj, afterIndices_card hj hk]

theorem afterLabels_01 (f : Fin 49 → Fin N) : afterLabels f 0 1 = {f 1} := by
  have h : afterIndices 0 1 = {1} := by decide
  simp [afterLabels, h]

theorem afterLabels_11 (f : Fin 49 → Fin N) : afterLabels f 1 1 = {f 1, f 25} := by
  have h : afterIndices 1 1 = {1, 25} := by decide
  simp [afterLabels, h]

theorem afterLabels_02 (f : Fin 49 → Fin N) : afterLabels f 0 2 = {f 1, f 2} := by
  have h : afterIndices 0 2 = {1, 2} := by decide
  simp [afterLabels, h]

theorem afterLabels_12 (f : Fin 49 → Fin N) : afterLabels f 1 2 = {f 1, f 2, f 25} := by
  have h : afterIndices 1 2 = {1, 2, 25} := by decide
  simp [afterLabels, h]

theorem afterLabels_22 (f : Fin 49 → Fin N) : afterLabels f 2 2 = {f 1, f 2, f 25, f 26} := by
  have h : afterIndices 2 2 = {1, 2, 25, 26} := by decide
  simp [afterLabels, h]

theorem pivot_not_after (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    (j k : ℕ) : f 0 ∉ afterLabels f j k := by
  simp [afterLabels, Finset.mem_image, hinj.eq_iff, afterIndices]

theorem boundary_not_after (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    {j k : ℕ} (hj : j ≤ 23) (hk : k ≤ 3) : f (boundary j hj) ∉ afterLabels f j k := by
  simp only [afterLabels, Finset.mem_image, hinj.eq_iff, exists_eq_right,
    afterIndices, Finset.mem_filter, Finset.mem_univ, true_and, boundary]
  omega

noncomputable def oneEvent (f : Fin 49 → Fin N) (j k : ℕ) (hj : j ≤ 23) :
    Finset (Equiv.Perm (Fin N)) := beforeOne (f (boundary j hj)) (f 0) (afterLabels f j k)

noncomputable def twoEvent (f : Fin 49 → Fin N) (u : Fin N) (j k : ℕ) (hj : j ≤ 23) :
    Finset (Equiv.Perm (Fin N)) := beforeTwo u (f (boundary j hj)) (f 0) (afterLabels f j k)

theorem mem_oneEvent (f : Fin 49 → Fin N) (π : Equiv.Perm (Fin N))
    (j k : ℕ) (hj : j ≤ 23) :
    π ∈ oneEvent f j k hj ↔ π (f (boundary j hj)) < π (f 0) ∧
      ∀ i ∈ afterIndices j k, π (f 0) < π (f i) := by
  simp [oneEvent, beforeOne, afterLabels]

theorem mem_twoEvent (f : Fin 49 → Fin N) (u : Fin N) (π : Equiv.Perm (Fin N))
    (j k : ℕ) (hj : j ≤ 23) :
    π ∈ twoEvent f u j k hj ↔ π u < π (f 0) ∧ π ∈ oneEvent f j k hj := by
  simp [oneEvent, twoEvent, beforeOne, beforeTwo]

theorem probability_oneEvent (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    {j k : ℕ} (hj : j ≤ 23) (hk : k ≤ 3) :
    probability (oneEvent f j k hj) =
      1 / (((j + k : ℕ) : ℝ) + 2) / (((j + k : ℕ) : ℝ) + 1) := by
  rw [oneEvent, probability_beforeOne (fun h => by
    have := congrArg Fin.val (hinj h)
    simp [boundary] at this)
    (boundary_not_after f hinj hj hk) (pivot_not_after f hinj j k),
    afterLabels_card f hinj hj hk]
  exact (div_div _ _ _).symm

/-- All witness coincidences are handled by a single exact formula. -/
theorem probability_twoEvent (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    (u : Fin N) (hu : u ≠ f 0) {j k : ℕ} (hj : j ≤ 23) (hk : k ≤ 3) :
    probability (twoEvent f u j k hj) =
      if u = f (boundary j hj) then
        1 / (((j + k : ℕ) : ℝ) + 2) / (((j + k : ℕ) : ℝ) + 1)
      else if u ∈ afterLabels f j k then 0
      else 2 / (((j + k : ℕ) : ℝ) + 3) /
        (((j + k : ℕ) : ℝ) + 2) / (((j + k : ℕ) : ℝ) + 1) := by
  classical
  by_cases he : u = f (boundary j hj)
  · rw [if_pos he]
    have heq : twoEvent f u j k hj = oneEvent f j k hj := by
      ext π
      simp [twoEvent, oneEvent, beforeTwo, beforeOne, he]
    rw [heq, probability_oneEvent f hinj hj hk]
  · rw [if_neg he]
    by_cases hm : u ∈ afterLabels f j k
    · rw [if_pos hm]
      have heq : twoEvent f u j k hj = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro π hπ
        have hh := (Finset.mem_filter.mp hπ).2
        exact (not_lt_of_ge hh.1.le) (hh.2.2 u hm)
      rw [heq, probability_empty]
    · rw [if_neg hm, twoEvent, probability_beforeTwo he hu
        (fun h => by have := congrArg Fin.val (hinj h); simp [boundary] at this)
        hm (boundary_not_after f hinj hj hk) (pivot_not_after f hinj j k),
        afterLabels_card f hinj hj hk]
      rw [div_div, div_div, mul_assoc]

end SmpMax.General.LongGap

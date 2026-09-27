import SmpMax.General.LongGapEvents
import SmpMax.General.LongerLogCertificate

/-!
# Exhaustive witness-coincidence rows for the longer events

A witness either equals one of the twenty-four opposite-side labels or
lies outside them. No independence assumption is made about that witness.
-/

namespace SmpMax.General.LongGap

open FiniteProbability LongerLogCertificate

variable {N : ℕ}

theorem boundary_mem_after (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    (i j : Fin 24) :
    f (boundary i.val (by omega)) ∈ afterLabels f j.val 2 ↔ i.val < j.val := by
  simp only [afterLabels, Finset.mem_image, hinj.eq_iff, exists_eq_right,
    afterIndices, Finset.mem_filter, Finset.mem_univ, true_and, boundary]
  omega

theorem outside_not_after (f : Fin 49 → Fin N) (u : Fin N)
    (hu1 : u ≠ f 1) (hu2 : u ≠ f 2)
    (hout : ∀ i : Fin 24, u ≠ f (boundary i.val (by omega))) (j : Fin 24) :
    u ∉ afterLabels f j.val 2 := by
  intro hu
  obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
  have hx' := (Finset.mem_filter.mp hx).2
  rcases hx' with hx' | hx'
  · have hx12 : x = 1 ∨ x = 2 := by
      have : x.val = 1 ∨ x.val = 2 := by omega
      rcases this with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases hx12 with h | h
    · exact hu1 (hxu.symm.trans (congrArg f h))
    · exact hu2 (hxu.symm.trans (congrArg f h))
  · let i : Fin 24 := ⟨x.val - 25, by omega⟩
    have he : x = boundary i.val (by omega) := by
      apply Fin.ext
      dsimp [boundary, i]
      omega
    exact hout i (hxu.symm.trans (congrArg f he))

theorem eventWeight_cast (i j : ℕ) :
    (eventWeight i j : ℝ) =
      if j < i then 2 / ((j : ℝ) + 5) / ((j : ℝ) + 4) / ((j : ℝ) + 3)
      else if j = i then 1 / ((j : ℝ) + 4) / ((j : ℝ) + 3) else 0 := by
  unfold eventWeight
  split_ifs <;> push_cast <;> simp only [div_div, mul_assoc]

theorem exists_second_row (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    (u : Fin N) (hu0 : u ≠ f 0) (hu1 : u ≠ f 1) (hu2 : u ≠ f 2) :
    ∃ i : Fin 25, ∀ j : Fin 24,
      probability (twoEvent f u j.val 2 (by omega)) = (eventWeight i.val j.val : ℝ) := by
  classical
  by_cases hex : ∃ i : Fin 24, u = f (boundary i.val (by omega))
  · obtain ⟨i, rfl⟩ := hex
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    intro j
    have he : f (boundary i.val (by omega)) = f (boundary j.val (by omega)) ↔
        j.val = i.val := by
      rw [hinj.eq_iff, Fin.ext_iff]
      dsimp [boundary]
      omega
    rw [probability_twoEvent f hinj _ hu0 (by omega) (by omega), eventWeight_cast]
    simp only [he, boundary_mem_after f hinj]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    by_cases hlt : j.val < i.val
    · have hne : j.val ≠ i.val := by omega
      have hnlt : ¬ i.val < j.val := by omega
      simp only [hlt, hne, hnlt, if_true, if_false]
      ring_nf
    · by_cases heq : j.val = i.val
      · simp only [heq, lt_self_iff_false, ↓reduceIte]
        ring_nf
      · have hgt : i.val < j.val := by omega
        simp only [hlt, heq, hgt, if_true, if_false]
  · have hout : ∀ i : Fin 24, u ≠ f (boundary i.val (by omega)) := by
      simpa only [not_exists] using hex
    refine ⟨24, ?_⟩
    intro j
    rw [probability_twoEvent f hinj _ hu0 (by omega) (by omega),
      if_neg (hout j), if_neg (outside_not_after f u hu1 hu2 hout j), eventWeight_cast]
    have hj : j.val < (24 : Fin 25).val := j.isLt
    simp only [hj, if_true]
    push_cast
    ring_nf

end SmpMax.General.LongGap

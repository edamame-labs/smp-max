import SmpMax.General.BidirectionalLogCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Exact certificates for a longer-event saving and the base 3.18

The rational floors come from six positive terms of the logarithm series.
Lean verifies their lower-bound property and every witness-coincidence row.
-/

namespace SmpMax.General.LongerLogCertificate

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable def saving : ℝ := 467 / 20000
noncomputable def shortSaving : ℝ := shortSideSaving + logIncrement 3 / 15

def incrementLower (j : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range 6, (1 / (2 * (j : ℚ) + 3)) ^ (2 * i + 1) / (2 * i + 1)

def incrementFloor : ℕ → ℚ
  | 0 => 69314707 / 100000000
  | 1 => 40546510 / 100000000
  | 2 => 28768207 / 100000000
  | 3 => 22314355 / 100000000
  | 4 => 18232155 / 100000000
  | 5 => 15415067 / 100000000
  | 6 => 13353139 / 100000000
  | 7 => 11778303 / 100000000
  | 8 => 10536051 / 100000000
  | 9 => 9531017 / 100000000
  | 10 => 8701137 / 100000000
  | 11 => 8004270 / 100000000
  | 12 => 7410797 / 100000000
  | 13 => 6899287 / 100000000
  | 14 => 6453852 / 100000000
  | 15 => 6062462 / 100000000
  | 16 => 5715841 / 100000000
  | 17 => 5406722 / 100000000
  | 18 => 5129329 / 100000000
  | 19 => 4879016 / 100000000
  | 20 => 4652001 / 100000000
  | 21 => 4445176 / 100000000
  | 22 => 4255961 / 100000000
  | 23 => 4082199 / 100000000
  | 24 => 3922071 / 100000000
  | _ => 0

theorem incrementLower_le (j : ℕ) : (incrementLower j : ℝ) ≤ logIncrement j := by
  let x : ℝ := 1 / (2 * (j : ℝ) + 3)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have heq : (1 + x) / (1 - x) = (j + 2 : ℝ) / (j + 1 : ℝ) := by
    apply (div_eq_div_iff (ne_of_gt (sub_pos.mpr hx1)) (by positivity)).mpr
    dsimp [x]
    field_simp
    ring
  have h := Real.sum_range_le_log_div hx0 hx1 6
  rw [heq, ← logIncrement_eq_log_ratio] at h
  unfold incrementLower
  push_cast
  dsimp [x] at h
  linarith

theorem incrementFloor_le {j : ℕ} (hj : j ≤ 24) :
    (incrementFloor j : ℝ) ≤ logIncrement j := by
  have hq : incrementFloor j ≤ incrementLower j := by
    interval_cases j <;> norm_num [incrementFloor, incrementLower, Finset.sum_range_succ]
  have hr : (incrementFloor j : ℝ) ≤ (incrementLower j : ℝ) := by exact_mod_cast hq
  exact hr.trans (incrementLower_le j)

/-- Index 24 is the outside-witness row; indices 0,...,23 are coincidences. -/
def eventWeight (i j : ℕ) : ℚ :=
  if j < i then 2 / ((j + 5 : ℚ) * (j + 4) * (j + 3))
  else if j = i then 1 / ((j + 4 : ℚ) * (j + 3)) else 0

def rowLower (i : Fin 25) : ℚ :=
  ∑ j : Fin 24, eventWeight i.val j.val * incrementFloor (j.val + 1)

theorem eventWeight_nonneg (i j : ℕ) : 0 ≤ eventWeight i j := by
  unfold eventWeight
  split_ifs <;> positivity

theorem rowLower_ge (i : Fin 25) : (467 / 20000 : ℚ) ≤ rowLower i := by
  fin_cases i <;> norm_num [rowLower, eventWeight, incrementFloor, Fin.sum_univ_succ]

theorem row_saving_ge (i : Fin 25) :
    saving ≤ ∑ j : Fin 24, (eventWeight i.val j.val : ℝ) * logIncrement (j.val + 1) := by
  have hq : ((467 / 20000 : ℚ) : ℝ) ≤ (rowLower i : ℝ) := by
    exact_mod_cast rowLower_ge i
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hq
  have hb : (rowLower i : ℝ) ≤
      ∑ j : Fin 24, (eventWeight i.val j.val : ℝ) * logIncrement (j.val + 1) := by
    unfold rowLower
    push_cast
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left (incrementFloor_le (by omega))
    exact_mod_cast eventWeight_nonneg i.val j.val
  exact hq.trans hb

theorem saving_nonneg : 0 ≤ saving := by norm_num [saving]

theorem shortSaving_ge_three : 3 * saving ≤ shortSaving := by
  have h1 := incrementFloor_le (by omega : 1 ≤ 24)
  have h2 := incrementFloor_le (by omega : 2 ≤ 24)
  have h3 := incrementFloor_le (by omega : 3 ≤ 24)
  norm_num [incrementFloor] at h1 h2 h3
  unfold saving shortSaving shortSideSaving
  linarith

theorem firstSaving_ge_three : 3 * saving ≤ BidirectionalLogCertificate.firstStepSaving := by
  have h0 := incrementFloor_le (by omega : 0 ≤ 24)
  have h1 := incrementFloor_le (by omega : 1 ≤ 24)
  norm_num [incrementFloor, logIncrement] at h0 h1
  unfold saving BidirectionalLogCertificate.firstStepSaving logIncrement
  norm_num only
  linarith

theorem refinedLogBound_sub_two_savings_lt_log :
    refinedLogBound 512 - 2 * saving < Real.log (159 / 50 : ℝ) := by
  let x : ℝ := 25329 / 1085329
  have h := Real.log_div_le_sum_range_add (x := x) (by norm_num [x]) (by norm_num [x]) 4
  have he : (1 + x) / (1 - x) = (1665987 / 500000 : ℝ) / (159 / 50) := by norm_num [x]
  rw [he, Real.log_div (by norm_num) (by norm_num)] at h
  have hs : (∑ i ∈ Finset.range 4, x ^ (2 * i + 1) / (2 * i + 1)) +
      x ^ (2 * 4 + 1) / (1 - x ^ 2) < saving := by
    norm_num [x, saving, Finset.sum_range_succ]
  have hold := RefinedLogCertificate.refinedLogBound_512_lt_log
  linarith

end SmpMax.General.LongerLogCertificate

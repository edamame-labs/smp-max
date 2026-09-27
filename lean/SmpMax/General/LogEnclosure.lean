import SmpMax.General.LogCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Rational enclosures for the finite logarithmic constant

The analytic remainder follows from Mathlib's proved logarithm series
bound. Six terms suffice for the increments; the target uses sixteen
terms for a lower bound. Every subsequent numerical inequality is checked
by Lean, independently of the program which supplies proposed bounds.
-/

namespace SmpMax.General.LogCertificate

def upperTerm (j : ℕ) : ℚ :=
  let x := 1 / (2 * (j : ℚ) + 3)
  4 / (j + 3 : ℚ) *
    (x + x^3/3 + x^5/5 + x^7/7 + x^9/9 + x^11/11 + x^13/(1-x^2))

theorem gapTerm_le_upperTerm (j : ℕ) : gapTerm j ≤ (upperTerm j : ℝ) := by
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
  have h := Real.log_div_le_sum_range_add hx0 hx1 6
  norm_num [Finset.sum_range_succ] at h
  rw [heq, ← logIncrement_eq_log_ratio] at h
  calc
    gapTerm j = 4 / (j + 3 : ℝ) * (1 / 2 * logIncrement j) := by unfold gapTerm; ring
    _ ≤ 4 / (j + 3 : ℝ) *
        (x + x^3/3 + x^5/5 + x^7/7 + x^9/9 + x^11/11 + x^13/(1-x^2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by unfold upperTerm; push_cast; rfl

def targetLower : ℚ :=
  2 * ∑ i ∈ Finset.range 16, (583 / 1083 : ℚ) ^ (2 * i + 1) / (2 * i + 1)

theorem targetLower_le_log : (targetLower : ℝ) ≤ Real.log (833 / 250 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := 583 / 1083) (by norm_num) (by norm_num) 16
  have heq : (1 + (583 / 1083 : ℝ)) / (1 - 583 / 1083) = 833 / 250 := by norm_num
  rw [heq] at h
  unfold targetLower
  push_cast
  linarith

end SmpMax.General.LogCertificate

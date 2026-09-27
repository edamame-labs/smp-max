import SmpMax.General.ShortSideSaving
import SmpMax.General.RefinedLogCertificate

/-!
# Exact arithmetic for the proposed structural bound

These statements certify the saving comparisons and the final numerical
step. They do not assert the unfinished all-order structural counting theorem.
-/

namespace SmpMax.General.StructuralLogCertificate

noncomputable def saving : ℝ := Real.log 3 / 60

theorem saving_nonneg : 0 ≤ saving := by
  unfold saving
  exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)

private theorem log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

theorem shortSideSaving_ge_three : 3 * saving ≤ shortSideSaving := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 4)
    (by norm_num : (3 : ℝ) ^ 4 ≤ 2 ^ 7)
  simp only [Real.log_pow] at h
  norm_num at h
  unfold shortSideSaving logIncrement saving
  norm_num only
  rw [log_four]
  linarith

theorem first_step_saving_ge_three : 3 * saving ≤ Real.log 2 / 12 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 3)
    (by norm_num : (3 : ℝ) ^ 3 ≤ 2 ^ 5)
  simp only [Real.log_pow] at h
  norm_num at h
  unfold saving
  linarith

theorem second_step_saving_eq : logIncrement 1 / 30 + logIncrement 2 / 60 = saving := by
  unfold logIncrement saving
  norm_num only
  rw [log_four]
  ring

theorem boundary_saving_ge : saving ≤ logIncrement 1 / 12 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 5)
    (by norm_num : (2 : ℝ) ^ 5 ≤ 3 ^ 4)
  simp only [Real.log_pow] at h
  norm_num at h
  unfold saving logIncrement
  norm_num only
  linarith

theorem rational_power_comparison :
    (1665987 / 500000 : ℝ) ^ 60 < 3 * (409 / 125 : ℝ) ^ 60 := by
  norm_num

/-- The certified old logarithmic bound minus the new saving is below log 3.272. -/
theorem refinedLogBound_sub_saving_lt_log :
    refinedLogBound 512 - saving < Real.log (409 / 125 : ℝ) := by
  have hold := RefinedLogCertificate.refinedLogBound_512_lt_log
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < (1665987 / 500000 : ℝ) ^ 60)
    rational_power_comparison
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at h
  norm_num only at h
  unfold saving
  linarith

end SmpMax.General.StructuralLogCertificate

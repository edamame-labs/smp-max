import SmpMax.General.StructuralLogCertificate

/-!
# Arithmetic for two directional savings and a base of 3.2

The full matching-count theorem is not asserted here. These lemmas verify
the strengthened local saving comparisons and the resulting numerical step.
-/

namespace SmpMax.General.BidirectionalLogCertificate

noncomputable def saving : ℝ :=
  StructuralLogCertificate.saving + logIncrement 3 / 105

noncomputable def firstStepSaving : ℝ := Real.log 2 / 12 + logIncrement 1 / 30

theorem saving_nonneg : 0 ≤ saving :=
  add_nonneg StructuralLogCertificate.saving_nonneg
    (div_nonneg (logIncrement_nonneg 3) (by norm_num))

private theorem log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

theorem shortSideSaving_ge_three : 3 * saving ≤ shortSideSaving := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 28 * 5 ^ 12)
    (by norm_num : (3 : ℝ) ^ 28 * 5 ^ 12 ≤ 2 ^ 73)
  rw [Real.log_mul (by positivity) (by positivity)] at h
  simp only [Real.log_pow] at h
  norm_num only at h
  unfold saving StructuralLogCertificate.saving shortSideSaving logIncrement
  norm_num only
  rw [log_four]
  linarith

theorem firstStepSaving_ge_three : 3 * saving ≤ firstStepSaving := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 7 * 5 ^ 12)
    (by norm_num : (3 : ℝ) ^ 7 * 5 ^ 12 ≤ 2 ^ 45)
  rw [Real.log_mul (by positivity) (by positivity)] at h
  simp only [Real.log_pow] at h
  norm_num only at h
  unfold saving StructuralLogCertificate.saving firstStepSaving logIncrement
  norm_num only
  rw [log_four]
  linarith

theorem secondStepSaving_eq :
    logIncrement 1 / 30 + logIncrement 2 / 60 + logIncrement 3 / 105 = saving := by
  rw [StructuralLogCertificate.second_step_saving_eq]
  rfl

theorem firstStepSaving_le_first_coincidence : firstStepSaving ≤ Real.log 2 / 6 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 2)
    (by norm_num : (3 : ℝ) ^ 2 ≤ 2 ^ 7)
  simp only [Real.log_pow] at h
  norm_num only at h
  unfold firstStepSaving logIncrement
  norm_num only
  linarith

theorem saving_le_first_coincidence : saving ≤ logIncrement 1 / 12 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 27 * 5 ^ 4)
    (by norm_num : (2 : ℝ) ^ 27 * 5 ^ 4 ≤ 3 ^ 28)
  rw [Real.log_mul (by positivity) (by positivity)] at h
  simp only [Real.log_pow] at h
  norm_num only at h
  unfold saving StructuralLogCertificate.saving logIncrement
  norm_num only
  rw [log_four]
  linarith

theorem saving_le_second_coincidence :
    saving ≤ logIncrement 1 / 30 + logIncrement 2 / 20 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 7 * 5 ^ 2)
    (by norm_num : (3 : ℝ) ^ 7 * 5 ^ 2 ≤ 4 ^ 9)
  rw [Real.log_mul (by positivity) (by positivity)] at h
  simp only [Real.log_pow] at h
  norm_num only at h
  unfold saving StructuralLogCertificate.saving logIncrement
  norm_num only
  rw [log_four] at h ⊢
  linarith

theorem saving_le_third_coincidence :
    saving ≤ logIncrement 1 / 30 + logIncrement 2 / 60 + logIncrement 3 / 30 := by
  rw [← secondStepSaving_eq]
  linarith [logIncrement_nonneg 3]

theorem rational_power_comparison :
    (1665987 / 500000 : ℝ) ^ 210 <
      (3 ^ 7 * (5 / 4 : ℝ) ^ 4) * (16 / 5 : ℝ) ^ 210 := by
  norm_num

theorem refinedLogBound_sub_two_savings_lt_log :
    refinedLogBound 512 - 2 * saving < Real.log (16 / 5 : ℝ) := by
  have hold := RefinedLogCertificate.refinedLogBound_512_lt_log
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < (1665987 / 500000 : ℝ) ^ 210)
    rational_power_comparison
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h
  simp only [Real.log_pow] at h
  have hratio : Real.log (5 / 4 : ℝ) = Real.log 5 - Real.log 4 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [hratio] at h
  norm_num only at h
  unfold saving StructuralLogCertificate.saving logIncrement
  norm_num only
  linarith

end SmpMax.General.BidirectionalLogCertificate

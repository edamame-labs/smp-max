import SmpMax.General.LongerLogCertificate

/-!
# Exact margins for the simultaneous-cap saving and the base 3.178

The old directional saving is preserved. An additional rational saving
pays for the joint event after exception charging.
-/

namespace SmpMax.General.JointLogCertificate

open LongerLogCertificate

noncomputable def jointSaving : ℝ := 307 / 500000

theorem jointSaving_nonneg : 0 ≤ jointSaving := by norm_num [jointSaving]

theorem jointSaving_le : jointSaving ≤ Real.log (16 / 15 : ℝ) / 105 := by
  have h := incrementFloor_le (by omega : 14 ≤ 24)
  rw [logIncrement_eq_log_ratio] at h
  norm_num [incrementFloor] at h
  unfold jointSaving
  linarith

theorem short_ge : 3 * (saving + jointSaving) ≤ shortSaving := by
  have h1 := incrementFloor_le (by omega : 1 ≤ 24)
  have h2 := incrementFloor_le (by omega : 2 ≤ 24)
  have h3 := incrementFloor_le (by omega : 3 ≤ 24)
  norm_num [incrementFloor] at h1 h2 h3
  unfold saving jointSaving shortSaving shortSideSaving
  linarith

theorem first_zero_ge : 3 * (saving + jointSaving) ≤ logIncrement 0 / 6 := by
  have h := incrementFloor_le (by omega : 0 ≤ 24)
  norm_num [incrementFloor] at h
  unfold saving jointSaving
  linarith

theorem first_one_ge : 3 * (saving + jointSaving) ≤
    logIncrement 0 / 12 + logIncrement 1 / 12 := by
  have h0 := incrementFloor_le (by omega : 0 ≤ 24)
  have h1 := incrementFloor_le (by omega : 1 ≤ 24)
  norm_num [incrementFloor] at h0 h1
  unfold saving jointSaving
  linarith

theorem first_outside_ge : 3 * (saving + jointSaving) ≤
    logIncrement 0 / 12 + logIncrement 1 / 30 + logIncrement 2 / 60 := by
  have h0 := incrementFloor_le (by omega : 0 ≤ 24)
  have h1 := incrementFloor_le (by omega : 1 ≤ 24)
  have h2 := incrementFloor_le (by omega : 2 ≤ 24)
  norm_num [incrementFloor] at h0 h1 h2
  unfold saving jointSaving
  linarith

theorem second_zero_ge : saving + jointSaving ≤ logIncrement 1 / 12 := by
  have h := incrementFloor_le (by omega : 1 ≤ 24)
  norm_num [incrementFloor] at h
  unfold saving jointSaving
  linarith

theorem second_one_ge : saving + jointSaving ≤
    logIncrement 1 / 30 + logIncrement 2 / 20 := by
  have h1 := incrementFloor_le (by omega : 1 ≤ 24)
  have h2 := incrementFloor_le (by omega : 2 ≤ 24)
  norm_num [incrementFloor] at h1 h2
  unfold saving jointSaving
  linarith

theorem refinedLogBound_sub_savings_lt_log :
    refinedLogBound 512 - 2 * saving - jointSaving < Real.log (1589 / 500 : ℝ) := by
  let x : ℝ := 76987 / 3254987
  have h := Real.log_div_le_sum_range_add (x := x) (by norm_num [x]) (by norm_num [x]) 4
  have he : (1 + x) / (1 - x) = (1665987 / 500000 : ℝ) / (1589 / 500) := by
    norm_num [x]
  rw [he, Real.log_div (by norm_num) (by norm_num)] at h
  have hs : 2 * ((∑ i ∈ Finset.range 4, x ^ (2 * i + 1) / (2 * i + 1)) +
      x ^ (2 * 4 + 1) / (1 - x ^ 2)) < 2 * saving + jointSaving := by
    norm_num [x, saving, jointSaving, Finset.sum_range_succ]
  have hold := RefinedLogCertificate.refinedLogBound_512_lt_log
  linarith

end SmpMax.General.JointLogCertificate

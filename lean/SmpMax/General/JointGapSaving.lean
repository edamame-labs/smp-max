import SmpMax.General.BidirectionalGapSaving

/-!
# The positive remainder when both directional caps shrink

The two directional losses leave a nonnegative logarithmic remainder.
When both sides have length at least two and both caps are at most one,
this remainder is at least log(16/15).
-/

namespace SmpMax.General.JointGap

noncomputable def loss (L R l r : ℝ) : ℝ :=
  Real.log (1 + l + R) + Real.log (1 + L + r) -
    Real.log (1 + L + R) - Real.log (1 + l + r)

theorem loss_nonneg {L R l r : ℝ}
    (hl0 : 0 ≤ l) (hr0 : 0 ≤ r) (hl : l ≤ L) (hr : r ≤ R) :
    0 ≤ loss L R l r := by
  have h := BidirectionalGap.log_caps_superadditive hl0 hr0 hl hr
  unfold loss
  linarith

theorem loss_ge {L R l r : ℝ}
    (hl0 : 0 ≤ l) (hr0 : 0 ≤ r) (hL : 2 ≤ L) (hR : 2 ≤ R)
    (hl : l ≤ 1) (hr : r ≤ 1) : Real.log (16 / 15 : ℝ) ≤ loss L R l r := by
  have hp : (L - 1) * (R - 1) ≤ (L - l) * (R - r) := by
    apply mul_le_mul <;> linarith
  have hrect : 1 + L + R ≤ 5 * (L - 1) * (R - 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ L - 2) (by linarith : 0 ≤ R - 2)]
  have hc : (1 + L + R) * (1 + l + r) ≤ 3 * (1 + L + R) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + L + R)
      (by linarith : 0 ≤ 2 - l - r)]
  have hratio : (16 / 15 : ℝ) ≤
      ((1 + l + R) * (1 + L + r)) / ((1 + L + R) * (1 + l + r)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16 / 15) hratio
  rw [Real.log_div (x := (1 + l + R) * (1 + L + r))
      (y := (1 + L + R) * (1 + l + r)) (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h
  unfold loss
  linarith

end SmpMax.General.JointGap

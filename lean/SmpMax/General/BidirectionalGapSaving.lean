import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Combining both directional gap losses

Both losses use the same reference gap. The product identity proves that
their sum does not overcount the reduction in the final support.
-/

namespace SmpMax.General.BidirectionalGap

theorem log_caps_superadditive {L R l r : ℝ}
    (hl0 : 0 ≤ l) (hr0 : 0 ≤ r) (hl : l ≤ L) (hr : r ≤ R) :
    (Real.log (1 + L + R) - Real.log (1 + l + R)) +
      (Real.log (1 + L + R) - Real.log (1 + L + r)) ≤
      Real.log (1 + L + R) - Real.log (1 + l + r) := by
  have hL : 0 ≤ L := hl0.trans hl
  have hR : 0 ≤ R := hr0.trans hr
  have hp : (1 + L + R) * (1 + l + r) ≤ (1 + l + R) * (1 + L + r) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (1 + L + R) * (1 + l + r)) hp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hlog
  linarith

theorem log_support_le_sub_losses {L R l r X : ℝ}
    (hl0 : 0 ≤ l) (hr0 : 0 ≤ r) (hl : l ≤ L) (hr : r ≤ R)
    (hX0 : 0 < X) (hX : X ≤ 1 + l + r) :
    Real.log X ≤ Real.log (1 + L + R) -
      (Real.log (1 + L + R) - Real.log (1 + l + R)) -
      (Real.log (1 + L + R) - Real.log (1 + L + r)) := by
  have hc := log_caps_superadditive hl0 hr0 hl hr
  have hx := Real.log_le_log hX0 hX
  linarith

theorem directional_loss_ge {L R r q k : ℝ}
    (hL : 0 ≤ L) (hr0 : 0 ≤ r) (hq : r ≤ q) (hk : k ≤ R) (hk0 : 0 ≤ k) :
    Real.log (1 + L + k) - Real.log (1 + L + q) ≤
      Real.log (1 + L + R) - Real.log (1 + L + r) := by
  have htop := Real.log_le_log (by positivity : (0 : ℝ) < 1 + L + k)
    (by linarith : 1 + L + k ≤ 1 + L + R)
  have hbottom := Real.log_le_log (by positivity : (0 : ℝ) < 1 + L + r)
    (by linarith : 1 + L + r ≤ 1 + L + q)
  linarith

end SmpMax.General.BidirectionalGap

import SmpMax.General.PermutationRevelation
import SmpMax.General.LogCertificate

/-!
# The general 3.332 exponential upper bound

For every positive order and complete strict balanced preference profile,
the number of stable matchings is strictly less than (833/250)^n.
All combinatorial, analytic, and numerical obligations are Lean theorems.
No external certificate or unproved structural hypothesis is assumed.
-/

namespace SmpMax.General

/-- Every complete strict balanced instance has fewer than 3.332^n stable matchings. -/
theorem stableCount_lt_3332_pow {n : ℕ} (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (833 / 250 : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ Real.exp (n * finiteLogBound 512) :=
      stableCount_le_exp_finiteLogBound I (by norm_num)
    _ < Real.exp (n * Real.log (833 / 250 : ℝ)) :=
      Real.exp_lt_exp.mpr
        (mul_lt_mul_of_pos_left LogCertificate.finiteLogBound_512_lt_log hnR)
    _ = _ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 833 / 250)]

end SmpMax.General

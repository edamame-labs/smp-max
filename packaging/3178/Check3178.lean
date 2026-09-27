import SmpMax.General.JointEntropyUpperBound

/-!
The complete public statement, with every hypothesis explicit.
The denominator is exactly 500; 1589/500 is exactly 3.178.
-/

#check @SmpMax.General.stableCount_lt_3178_pow
#print axioms SmpMax.General.stableCount_lt_3178_pow

example : ∀ n : ℕ, 0 < n → ∀ I : SmpMax.General.Profile n,
    (SmpMax.General.stableCount I : ℝ) < (1589 / 500 : ℝ) ^ n :=
  fun _n hn I => SmpMax.General.stableCount_lt_3178_pow hn I

#print SmpMax.General.Profile
#print SmpMax.General.Matching
#print SmpMax.General.Blocks
#print SmpMax.General.Stable
#print SmpMax.General.stableMatchings
#print SmpMax.General.stableCount

import SmpMax.General.GapTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite logarithmic tail sums

The logarithm of a positive integer telescopes over threshold indicators.
Uniform finite averages then use the proved gap tail. There is no exchange
of infinite sums and expectations.
-/

namespace SmpMax.General

open FiniteProbability

noncomputable def logIncrement (j : ℕ) : ℝ :=
  Real.log (j + 2 : ℝ) - Real.log (j + 1 : ℝ)

theorem logIncrement_eq_log_ratio (j : ℕ) :
    logIncrement j = Real.log ((j + 2 : ℝ) / (j + 1 : ℝ)) := by
  rw [Real.log_div (by positivity) (by positivity)]
  rfl

theorem logIncrement_nonneg (j : ℕ) : 0 ≤ logIncrement j := by
  apply sub_nonneg.mpr
  exact Real.log_le_log (by positivity) (by linarith)

/-- The finite threshold expansion for any function on positive integers. -/
theorem sum_threshold_differences (f : ℕ → ℝ) {D K : ℕ}
    (hK : 0 < K) (hKD : K ≤ D + 1) :
    (∑ j ∈ Finset.range D, if j + 2 ≤ K then f (j + 2) - f (j + 1) else 0) =
      f K - f 1 := by
  induction D generalizing K with
  | zero =>
    have h : K = 1 := by omega
    simp [h]
  | succ D ih =>
    rw [Finset.sum_range_succ]
    by_cases hsmall : K ≤ D + 1
    · rw [ih hK hsmall, if_neg (by omega)]
      simp
    · have heq : K = D + 2 := by omega
      subst K
      have hprev := ih (show 0 < D + 1 by omega) (le_refl (D + 1))
      have heqsum :
          (∑ j ∈ Finset.range D, if j + 2 ≤ D + 2 then f (j + 2) - f (j + 1) else 0) =
          ∑ j ∈ Finset.range D, if j + 2 ≤ D + 1 then f (j + 2) - f (j + 1) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjD := Finset.mem_range.mp hj
        rw [if_pos (by omega), if_pos (by omega)]
      rw [heqsum, hprev, if_pos (by omega)]
      ring

theorem log_nat_eq_threshold_sum {D K : ℕ} (hK : 0 < K) (hKD : K ≤ D + 1) :
    Real.log K = ∑ j ∈ Finset.range D, if j + 2 ≤ K then logIncrement j else 0 := by
  have h := sum_threshold_differences (fun k => Real.log k) hK hKD
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Real.log_one, sub_zero,
    logIncrement] using h.symm

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def threshold (K : Ω → ℕ) (k : ℕ) : Finset Ω :=
  Finset.univ.filter (fun x => k ≤ K x)

omit [Nonempty Ω] in
theorem average_threshold (K : Ω → ℕ) (k : ℕ) (c : ℝ) :
    average (fun x => if k ≤ K x then c else 0) = probability (threshold K k) * c := by
  unfold average probability threshold
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

omit [Nonempty Ω] in
/-- Exact finite tail-sum identity for the expected logarithm. -/
theorem average_log_eq_tail_sum (K : Ω → ℕ) (D : ℕ)
    (hpos : ∀ x, 0 < K x) (hle : ∀ x, K x ≤ D + 1) :
    average (fun x => Real.log (K x)) =
      ∑ j ∈ Finset.range D, probability (threshold K (j + 2)) * logIncrement j := by
  have heq : (fun x => Real.log (K x)) =
      (fun x => ∑ j ∈ Finset.range D, if j + 2 ≤ K x then logIncrement j else 0) := by
    funext x
    exact log_nat_eq_threshold_sum (hpos x) (hle x)
  rw [heq, average_finset_sum]
  exact Finset.sum_congr rfl (fun j _ => average_threshold K (j + 2) (logIncrement j))

end FiniteProbability

noncomputable def gapTerm (j : ℕ) : ℝ := 2 / (j + 3 : ℝ) * logIncrement j

noncomputable def partialLogBound (D : ℕ) : ℝ := ∑ j ∈ Finset.range D, gapTerm j

theorem Gap.average_log_size_le_partial {d n : ℕ} (owner : Fin d → Fin n)
    (hinj : Function.Injective owner) (t : Fin d) :
    average (fun π => Real.log (Gap.size (Gap.revealedBy owner π t) t)) ≤
      partialLogBound d := by
  rw [average_log_eq_tail_sum _ d (fun π => Gap.size_pos _ _)
    (fun π => (Gap.size_le_length _ _).trans (Nat.le_succ d))]
  apply Finset.sum_le_sum
  intro j _
  have h := Gap.probability_size_ge_le owner hinj t (show 0 < j + 2 by omega)
  have hcast : ((j + 2 : ℕ) : ℝ) + 1 = (j : ℝ) + 3 := by push_cast; ring
  rw [hcast] at h
  exact mul_le_mul_of_nonneg_right h (logIncrement_nonneg j)

end SmpMax.General

import SmpMax.General.LogTail

/-!
# A finite cutoff bound uniform in the list length

Each logarithmic increment is at most 1/(j+1). The resulting rational
tail telescopes. A cutoff N uses the terms with ratios 2/1 through
N/(N-1), plus the explicit error 1/N + 1/(N+1).
-/

namespace SmpMax.General

theorem gapTerm_nonneg (j : ℕ) : 0 ≤ gapTerm j :=
  mul_nonneg (by positivity) (logIncrement_nonneg j)

theorem logIncrement_le_reciprocal (j : ℕ) : logIncrement j ≤ 1 / (j + 1 : ℝ) := by
  rw [logIncrement_eq_log_ratio]
  have h := Real.log_le_sub_one_of_pos (show 0 < (j + 2 : ℝ) / (j + 1 : ℝ) by positivity)
  have heq : (j + 2 : ℝ) / (j + 1 : ℝ) - 1 = 1 / (j + 1 : ℝ) := by
    field_simp
    ring
  rwa [heq] at h

theorem gapTerm_le_difference (j : ℕ) :
    gapTerm j ≤ 1 / (j + 1 : ℝ) - 1 / (j + 3 : ℝ) := by
  calc
    _ ≤ 2 / (j + 3 : ℝ) * (1 / (j + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (logIncrement_le_reciprocal j) (by positivity)
    _ = _ := by field_simp; ring

/-- A finite telescoping estimate, retaining the terminal subtractions. -/
theorem shifted_gap_sum_le (a l : ℕ) :
    (∑ j ∈ Finset.range l, gapTerm (a + j)) ≤
      1 / (a + 1 : ℝ) + 1 / (a + 2 : ℝ) -
        1 / (a + l + 1 : ℝ) - 1 / (a + l + 2 : ℝ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ]
    have h := add_le_add ih (gapTerm_le_difference (a + l))
    calc
      _ ≤ _ := h
      _ = _ := by push_cast; ring

theorem partialLogBound_mono {D M : ℕ} (hDM : D ≤ M) :
    partialLogBound D ≤ partialLogBound M := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hDM)
  intro j _ _
  exact gapTerm_nonneg j

/-- N here counts the retained increments; the numeric cutoff below is N+1. -/
theorem partialLogBound_le_cutoff (D M : ℕ) :
    partialLogBound D ≤ partialLogBound M + 1 / (M + 1 : ℝ) + 1 / (M + 2 : ℝ) := by
  by_cases hDM : D ≤ M
  · have h := partialLogBound_mono hDM
    have h1 : (0 : ℝ) ≤ 1 / (M + 1 : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / (M + 2 : ℝ) := by positivity
    linarith
  · have hMD : M ≤ D := by omega
    have heq : D = M + (D - M) := by omega
    have htail := shifted_gap_sum_le M (D - M)
    have h1 : (0 : ℝ) ≤ 1 / (M + (D - M : ℕ) + 1 : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 1 / (M + (D - M : ℕ) + 2 : ℝ) := by positivity
    have hsplit : partialLogBound D = partialLogBound M +
        ∑ j ∈ Finset.range (D - M), gapTerm (M + j) := by
      unfold partialLogBound
      conv_lhs => rw [heq, Finset.sum_range_add]
    linarith

noncomputable def finiteLogBound (N : ℕ) : ℝ :=
  partialLogBound (N - 1) + 1 / (N : ℝ) + 1 / (N + 1 : ℝ)

theorem partialLogBound_le_finiteLogBound (D : ℕ) {N : ℕ} (hN : 0 < N) :
    partialLogBound D ≤ finiteLogBound N := by
  have h := partialLogBound_le_cutoff D (N - 1)
  have heq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  unfold finiteLogBound
  rw [heq] at h
  convert h using 1 <;> first | rfl | (congr 1 <;> ring)

/-- The expected logarithmic gap is bounded at every positive fixed cutoff. -/
theorem Gap.average_log_size_le_finiteLogBound {d n : ℕ} (owner : Fin d → Fin n)
    (hinj : Function.Injective owner) (t : Fin d) {N : ℕ} (hN : 0 < N) :
    FiniteProbability.average (fun π => Real.log (Gap.size (Gap.revealedBy owner π t) t)) ≤
      finiteLogBound N :=
  (Gap.average_log_size_le_partial owner hinj t).trans
    (partialLogBound_le_finiteLogBound d hN)

end SmpMax.General

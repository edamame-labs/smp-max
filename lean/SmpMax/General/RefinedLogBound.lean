import SmpMax.General.LogEnclosure

/-!
# A sharper finite logarithmic remainder

The same gap-tail estimate has a smaller rational remainder. Applying the
proved logarithm-series enclosure with zero retained terms gives the
trapezoidal bound for each logarithmic increment. Its weighted sum telescopes.
This changes only the analytic enclosure, not the matching or probability model.
-/

namespace SmpMax.General

noncomputable def refinedTail (j : ℕ) : ℝ :=
  1 / (2 * (j + 1 : ℝ)) + 3 / (2 * (j + 2 : ℝ))

theorem refinedTail_nonneg (j : ℕ) : 0 ≤ refinedTail j := by
  unfold refinedTail
  positivity

theorem gapTerm_le_refined_difference (j : ℕ) :
    gapTerm j ≤ refinedTail j - refinedTail (j + 1) := by
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
  have h := Real.log_div_le_sum_range_add hx0 hx1 0
  norm_num at h
  rw [heq, ← logIncrement_eq_log_ratio] at h
  have hden : 1 - x ^ 2 =
      4 * (j + 1 : ℝ) * (j + 2 : ℝ) / (2 * (j : ℝ) + 3) ^ 2 := by
    dsimp [x]
    field_simp
    ring
  calc
    gapTerm j = 4 / (j + 3 : ℝ) * (1 / 2 * logIncrement j) := by
      unfold gapTerm
      ring
    _ ≤ 4 / (j + 3 : ℝ) * (x / (1 - x ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = refinedTail j - refinedTail (j + 1) := by
      rw [hden]
      dsimp [x, refinedTail]
      push_cast
      field_simp
      ring

theorem shifted_gap_sum_le_refined (a l : ℕ) :
    (∑ j ∈ Finset.range l, gapTerm (a + j)) ≤
      refinedTail a - refinedTail (a + l) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ]
    have h := add_le_add ih (gapTerm_le_refined_difference (a + l))
    have heq : a + (l + 1) = a + l + 1 := by omega
    rw [heq]
    linarith

theorem partialLogBound_le_refined_cutoff (D M : ℕ) :
    partialLogBound D ≤ partialLogBound M + refinedTail M := by
  by_cases hDM : D ≤ M
  · exact (partialLogBound_mono hDM).trans
      (le_add_of_nonneg_right (refinedTail_nonneg M))
  · have hMD : M ≤ D := by omega
    have heq : D = M + (D - M) := by omega
    have htail := shifted_gap_sum_le_refined M (D - M)
    have hnonneg := refinedTail_nonneg (M + (D - M))
    have hsplit : partialLogBound D = partialLogBound M +
        ∑ j ∈ Finset.range (D - M), gapTerm (M + j) := by
      unfold partialLogBound
      conv_lhs => rw [heq, Finset.sum_range_add]
    linarith

noncomputable def refinedLogBound (N : ℕ) : ℝ :=
  partialLogBound (N - 1) + 1 / (2 * (N : ℝ)) + 3 / (2 * (N + 1 : ℝ))

theorem partialLogBound_le_refinedLogBound (D : ℕ) {N : ℕ} (hN : 0 < N) :
    partialLogBound D ≤ refinedLogBound N := by
  have h := partialLogBound_le_refined_cutoff D (N - 1)
  have heq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  unfold refinedTail at h
  rw [heq] at h
  unfold refinedLogBound
  convert h using 1 <;> ring

theorem Gap.average_log_size_le_refinedLogBound {d n : ℕ} (owner : Fin d → Fin n)
    (hinj : Function.Injective owner) (t : Fin d) {N : ℕ} (hN : 0 < N) :
    FiniteProbability.average (fun π => Real.log (Gap.size (Gap.revealedBy owner π t) t)) ≤
      refinedLogBound N :=
  (Gap.average_log_size_le_partial owner hinj t).trans
    (partialLogBound_le_refinedLogBound d hN)

end SmpMax.General

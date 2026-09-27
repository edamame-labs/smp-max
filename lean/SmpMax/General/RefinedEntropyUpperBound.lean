import SmpMax.General.PermutationRevelation
import SmpMax.General.RefinedLogCertificate

/-!
# The refined general 3.331974 upper bound

The fixed-men revelation argument is unchanged. A sharper finite remainder
and rational certificate improve the rounded base. The abstract averaging
lemma also exposes the precise obligation for any future structural improvement.
-/

namespace SmpMax.General

open FiniteProbability

variable {n : ℕ}

/-- Any uniform bound on the actual mean log support gives a counting bound. -/
theorem stableCount_le_exp_of_average_log_support (I : Profile n) (C : ℝ)
    (hC : ∀ μ : Matching n, Stable I μ → ∀ m : Fin n,
      average (fun π => Real.log (partnerSupportFinset I μ (earlierMen π m) m).card) ≤ C) :
    (stableCount I : ℝ) ≤ Real.exp (n * C) := by
  classical
  have hπ (π : Equiv.Perm (Fin n)) :
      (stableCount I : ℝ) * Real.log (stableCount I) ≤
        ∑ μ ∈ stableMatchings I, ∑ m,
          Real.log (partnerSupportFinset I μ (earlierMen π m) m).card := by
    have h := stableCount_mul_log_le_sum_supportCost I (revelationOrder π)
      (revelationOrder_covers π)
    simpa only [supportCost_eq_rank_sum] using h
  have havg := average_mono hπ
  rw [average_const, average_finset_sum] at havg
  have hbound :
      (∑ μ ∈ stableMatchings I,
        average (fun π => ∑ m,
          Real.log (partnerSupportFinset I μ (earlierMen π m) m).card)) ≤
        (stableCount I : ℝ) * (n * C) := by
    calc
      _ ≤ ∑ _μ ∈ stableMatchings I, ∑ _m : Fin n, C := by
        apply Finset.sum_le_sum
        intro μ hμ
        rw [average_finset_sum]
        exact Finset.sum_le_sum (fun m _ => hC μ (Finset.mem_filter.mp hμ).2 m)
      _ = _ := by simp [stableCount]
  have h := havg.trans hbound
  by_cases hz : stableCount I = 0
  · simp only [hz, Nat.cast_zero]
    exact (Real.exp_pos _).le
  · have hp : (0 : ℝ) < stableCount I := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (Real.log_le_iff_le_exp hp).mp (le_of_mul_le_mul_left h hp)

theorem stableCount_le_exp_refinedLogBound (I : Profile n) {N : ℕ} (hN : 0 < N) :
    (stableCount I : ℝ) ≤ Real.exp (n * refinedLogBound N) := by
  apply stableCount_le_exp_of_average_log_support
  intro μ hμ m
  let L := orderedPartners I m
  obtain ⟨t, ht⟩ := L.complete (μ m) (hμ.stablePair m)
  let owner := fun j => μ.symm (L.partner j)
  have hrev (π : Equiv.Perm (Fin n)) :
      Gap.revealedBy owner π t = L.revealedPositions μ π := by
    ext j
    simp [Gap.revealedBy, PartnerOrder.revealedPositions, earlierMen, owner, ht]
  have hgap := Gap.average_log_size_le_refinedLogBound owner (L.owners_injective μ) t hN
  apply le_trans (average_mono (fun π => ?_)) hgap
  apply Real.log_le_log (by exact_mod_cast hμ.support_card_pos (earlierMen π m) m)
  rw [hrev]
  exact_mod_cast L.support_card_le_revelationGap hμ π ht

/-- Every complete strict balanced instance has fewer than 3.331974^n stable matchings. -/
theorem stableCount_lt_3331974_pow (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (1665987 / 500000 : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ Real.exp (n * refinedLogBound 512) :=
      stableCount_le_exp_refinedLogBound I (by norm_num)
    _ < Real.exp (n * Real.log (1665987 / 500000 : ℝ)) :=
      Real.exp_lt_exp.mpr
        (mul_lt_mul_of_pos_left RefinedLogCertificate.refinedLogBound_512_lt_log hnR)
    _ = _ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 1665987 / 500000)]

end SmpMax.General

import SmpMax.General.MatchingRevelation
import SmpMax.General.LogCutoff
import Mathlib.Data.List.FinRange

/-!
# Averaging revelation costs over permutations of the fixed men

The order corresponding to a rank permutation reveals each man exactly
once. Its recursive prefix cost equals the sum using `earlierMen` for
each man. This connects the finite counting and gap arguments.
-/

namespace SmpMax.General

open FiniteProbability

variable {n : ℕ}

def revelationOrder (π : Equiv.Perm (Fin n)) : List (Fin n) :=
  (List.finRange n).map π.symm

theorem revelationOrder_covers (π : Equiv.Perm (Fin n)) (m : Fin n) :
    m ∈ revelationOrder π := by
  exact List.mem_map.mpr ⟨π m, List.mem_finRange _, π.symm_apply_apply m⟩

theorem revelationOrder_pairwise (π : Equiv.Perm (Fin n)) :
    (revelationOrder π).Pairwise (fun a b => π a < π b) := by
  simpa only [revelationOrder, List.pairwise_map, Equiv.apply_symm_apply] using
    List.pairwise_lt_finRange n

theorem supportCost_eq_rank_sum_aux (I : Profile n) (μ : Matching n)
    (π : Equiv.Perm (Fin n)) (order : List (Fin n)) (R : Finset (Fin n))
    (hp : order.Pairwise (fun a b => π a < π b))
    (hc : ∀ u, u ∈ R ∨ u ∈ order)
    (hR : ∀ u ∈ R, ∀ v ∈ order, π u < π v) :
    supportCost I μ R order =
      (order.map (fun m => Real.log (partnerSupportFinset I μ (earlierMen π m) m).card)).sum := by
  induction order generalizing R with
  | nil => rfl
  | cons m rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hp
    have heq : R = earlierMen π m := by
      ext u
      constructor
      · intro hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR u hu m List.mem_cons_self⟩
      · intro hu
        have hlt := (Finset.mem_filter.mp hu).2
        rcases hc u with huR | huL
        · exact huR
        · rcases List.mem_cons.mp huL with rfl | huL
          · exact (lt_irrefl _ hlt).elim
          · exact (not_lt_of_ge (hhead u huL).le hlt).elim
    have hc' : ∀ u, u ∈ insert m R ∨ u ∈ rest := by
      intro u
      rcases hc u with hu | hu
      · exact Or.inl (Finset.mem_insert_of_mem hu)
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl (Finset.mem_insert_self _ _)
        · exact Or.inr hu
    have hR' : ∀ u ∈ insert m R, ∀ v ∈ rest, π u < π v := by
      intro u hu v hv
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hhead v hv
      · exact hR u hu v (List.mem_cons_of_mem _ hv)
    rw [supportCost, List.map_cons, List.sum_cons, ih _ hrest hc' hR', heq]

theorem supportCost_eq_rank_sum (I : Profile n) (μ : Matching n)
    (π : Equiv.Perm (Fin n)) :
    supportCost I μ ∅ (revelationOrder π) =
      ∑ m, Real.log (partnerSupportFinset I μ (earlierMen π m) m).card := by
  rw [supportCost_eq_rank_sum_aux I μ π _ ∅ (revelationOrder_pairwise π)
    (fun u => Or.inr (revelationOrder_covers π u)) (by simp)]
  have hp := (Equiv.Perm.map_finRange_perm π.symm).map
    (fun m => Real.log (partnerSupportFinset I μ (earlierMen π m) m).card)
  rw [show revelationOrder π = (List.finRange n).map π.symm from rfl]
  rw [hp.sum_eq, ← List.ofFn_eq_map, List.sum_ofFn]

/-- The actual support is nonempty along every reference stable matching. -/
theorem Stable.support_card_pos {I : Profile n} {μ : Matching n} (hμ : Stable I μ)
    (R : Finset (Fin n)) (m : Fin n) : 0 < (partnerSupportFinset I μ R m).card := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨μ m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ.mem_partnerSupport R m⟩⟩

theorem average_log_support_le_finiteLogBound {I : Profile n} {μ : Matching n}
    (hμ : Stable I μ) (m : Fin n) {N : ℕ} (hN : 0 < N) :
    average (fun π => Real.log (partnerSupportFinset I μ (earlierMen π m) m).card) ≤
      finiteLogBound N := by
  let L := orderedPartners I m
  obtain ⟨t, ht⟩ := L.complete (μ m) (hμ.stablePair m)
  let owner := fun j => μ.symm (L.partner j)
  have hrev (π : Equiv.Perm (Fin n)) :
      Gap.revealedBy owner π t = L.revealedPositions μ π := by
    ext j
    simp [Gap.revealedBy, PartnerOrder.revealedPositions, earlierMen, owner, ht]
  have hgap := Gap.average_log_size_le_finiteLogBound owner (L.owners_injective μ) t hN
  apply le_trans (average_mono (fun π => ?_)) hgap
  apply Real.log_le_log (by exact_mod_cast hμ.support_card_pos (earlierMen π m) m)
  rw [hrev]
  exact_mod_cast L.support_card_le_revelationGap hμ π ht

/-- The counting inequality averaged over all permutations of the fixed men. -/
theorem stableCount_mul_log_le_cutoff (I : Profile n) {N : ℕ} (hN : 0 < N) :
    (stableCount I : ℝ) * Real.log (stableCount I) ≤
      (stableCount I : ℝ) * (n * finiteLogBound N) := by
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
        (stableCount I : ℝ) * (n * finiteLogBound N) := by
    calc
      _ ≤ ∑ _μ ∈ stableMatchings I, ∑ _m : Fin n, finiteLogBound N := by
        apply Finset.sum_le_sum
        intro μ hμ
        rw [average_finset_sum]
        exact Finset.sum_le_sum (fun m _ =>
          average_log_support_le_finiteLogBound (Finset.mem_filter.mp hμ).2 m hN)
      _ = _ := by simp [stableCount]
  exact havg.trans hbound

/-- General exponential bound with an explicit finite analytic constant. -/
theorem stableCount_le_exp_finiteLogBound (I : Profile n) {N : ℕ} (hN : 0 < N) :
    (stableCount I : ℝ) ≤ Real.exp (n * finiteLogBound N) := by
  by_cases hz : stableCount I = 0
  · simp only [hz, Nat.cast_zero]
    exact (Real.exp_pos _).le
  · have hp : (0 : ℝ) < stableCount I := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hlog := le_of_mul_le_mul_left (stableCount_mul_log_le_cutoff I hN) hp
    exact (Real.log_le_iff_le_exp hp).mp hlog

end SmpMax.General

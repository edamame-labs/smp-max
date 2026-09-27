import SmpMax.General.MatchingDirectionalSaving

/-!
# The unconditional general 3.2 upper bound

The six auxiliary labels enlarge the random order, not the matching
instance. Both directional losses use one common gap. Their matching-level
charging sums reduce the finite entropy constant by two explicit savings.
-/

namespace SmpMax.General

open FiniteProbability

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

theorem PartnerFrame.log_support_le_two_losses (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (π : Equiv.Perm (Fin (n + 6))) :
    Real.log (partnerSupportFinset I μ (Padded.earlier π m) m).card ≤
      Real.log (Gap.size (F.paddedSeen π) (Padded.position F.t)) -
        (F.directional hμ false).loss π - (F.directional hμ true).loss π := by
  let L := Gap.leftSize (F.paddedSeen π) (Padded.position F.t)
  let R := Gap.rightSize (F.paddedSeen π) (Padded.position F.t)
  let l := F.cap false (Padded.earlier π m)
  let r := F.cap true (Padded.earlier π m)
  have hl : l ≤ L := F.cap_le_padded hμ false π
  have hr : r ≤ R := F.cap_le_padded hμ true π
  have hcard : (partnerSupportFinset I μ (Padded.earlier π m) m).card ≤ 1 + l + r := by
    rw [← F.L.image_indexSupport μ (Padded.earlier π m),
      Finset.card_image_of_injective _ F.L.injective]
    simpa only [l, r, PartnerFrame.cap, Bool.false_eq_true, ↓reduceIte] using
      SupportCaps.card_le (F.L.indexSupport μ (Padded.earlier π m)) F.t
  have h := BidirectionalGap.log_support_le_sub_losses
    (L := (L : ℝ)) (R := (R : ℝ)) (l := (l : ℝ)) (r := (r : ℝ))
    (X := (partnerSupportFinset I μ (Padded.earlier π m) m).card)
    (by positivity) (by positivity) (by exact_mod_cast hl) (by exact_mod_cast hr)
    (by exact_mod_cast hμ.support_card_pos (Padded.earlier π m) m) (by exact_mod_cast hcard)
  have hgap : (Gap.size (F.paddedSeen π) (Padded.position F.t) : ℝ) =
      1 + (L : ℝ) + R := by
    exact_mod_cast Gap.size_eq_one_add_sides (F.paddedSeen π) (Padded.position F.t)
  have hf : (F.directional hμ false).loss π =
      Real.log (1 + (L : ℝ) + R) - Real.log (1 + (l : ℝ) + R) := by
    change Real.log (1 + (R : ℝ) + L) - Real.log (1 + (R : ℝ) + l) = _
    congr 1 <;> congr 1 <;> ring
  have ht : (F.directional hμ true).loss π =
      Real.log (1 + (L : ℝ) + R) - Real.log (1 + (L : ℝ) + r) := rfl
  rw [hgap, hf, ht]
  exact h

theorem PartnerFrame.average_log_support_le_two_savings (F : PartnerFrame I μ m)
    (hμ : Stable I μ) {N : ℕ} (hN : 0 < N) :
    average (fun π => Real.log (partnerSupportFinset I μ (Padded.earlier π m) m).card) ≤
      refinedLogBound N - F.meanSaving hμ false - F.meanSaving hμ true := by
  classical
  have h := average_mono (F.log_support_le_two_losses hμ)
  rw [average_sub, average_sub] at h
  have hg := Gap.average_log_size_le_refinedLogBound F.paddedOwner
    F.paddedOwner_injective (Padded.position F.t) hN
  change average (fun π => Real.log (Gap.size (F.paddedSeen π) (Padded.position F.t))) ≤
    refinedLogBound N at hg
  change average (fun π => Real.log (partnerSupportFinset I μ (Padded.earlier π m) m).card) ≤
    average (fun π => Real.log (Gap.size (F.paddedSeen π) (Padded.position F.t))) -
      F.meanSaving hμ false - F.meanSaving hμ true at h
  linarith

theorem average_sum_log_support_le_bidirectional (hμ : Stable I μ) {N : ℕ} (hN : 0 < N) :
    average (fun π => ∑ m,
      Real.log (partnerSupportFinset I μ (Padded.earlier π m) m).card) ≤
      n * (refinedLogBound N - 2 * BidirectionalLogCertificate.saving) := by
  classical
  let F := partnerFrame hμ
  have hl := sum_directional_savings hμ F false
  have hr := sum_directional_savings hμ F true
  rw [average_finset_sum]
  calc
    _ ≤ ∑ m, (refinedLogBound N - (F m).meanSaving hμ false - (F m).meanSaving hμ true) :=
      Finset.sum_le_sum (fun m _ => (F m).average_log_support_le_two_savings hμ hN)
    _ = n * refinedLogBound N - (∑ m, (F m).meanSaving hμ false) -
        (∑ m, (F m).meanSaving hμ true) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp
    _ ≤ _ := by nlinarith

theorem stableCount_le_exp_bidirectionalLogBound (I : Profile n) {N : ℕ} (hN : 0 < N) :
    (stableCount I : ℝ) ≤
      Real.exp (n * (refinedLogBound N - 2 * BidirectionalLogCertificate.saving)) := by
  apply stableCount_le_exp_of_average_rank_sum I
    (fun (π : Equiv.Perm (Fin (n + 6))) u => π (Padded.realLabel u))
    (fun π => π.injective.comp Padded.realLabel_injective)
  intro μ hμ
  exact average_sum_log_support_le_bidirectional hμ hN

/-- Every complete strict balanced instance has fewer than 3.2^n stable matchings. -/
theorem stableCount_lt_32_pow (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (16 / 5 : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ Real.exp (n * (refinedLogBound 512 - 2 * BidirectionalLogCertificate.saving)) :=
      stableCount_le_exp_bidirectionalLogBound I (by norm_num)
    _ < Real.exp (n * Real.log (16 / 5 : ℝ)) := Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left
        BidirectionalLogCertificate.refinedLogBound_sub_two_savings_lt_log hnR)
    _ = _ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 16 / 5)]

end SmpMax.General

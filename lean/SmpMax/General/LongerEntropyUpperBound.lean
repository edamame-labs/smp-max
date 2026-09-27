import SmpMax.General.LongMatchingDirectionalSaving

/-!
# The unconditional general 3.18 upper bound

The forty-eight auxiliary labels enlarge the random order, not the matching
instance. Both directional losses use one common gap. Their matching-level
charging sums reduce the finite entropy constant by two explicit savings.
-/

namespace SmpMax.General

open FiniteProbability

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

-- Unfolding the longer padded gap requires more elaboration than the six-label case.
set_option maxHeartbeats 1000000 in
theorem PartnerFrame.log_support_le_long_losses (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (π : Equiv.Perm (Fin (n + 48))) :
    Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card ≤
      Real.log (Gap.size (F.longSeen π) (LongPadded.position F.t)) -
        (F.longDirectional hμ false).loss π - (F.longDirectional hμ true).loss π := by
  let L := Gap.leftSize (F.longSeen π) (LongPadded.position F.t)
  let R := Gap.rightSize (F.longSeen π) (LongPadded.position F.t)
  let l := F.cap false (LongPadded.earlier π m)
  let r := F.cap true (LongPadded.earlier π m)
  have hl : l ≤ L := F.cap_le_long_gap hμ false π
  have hr : r ≤ R := F.cap_le_long_gap hμ true π
  have hcard : (partnerSupportFinset I μ (LongPadded.earlier π m) m).card ≤ 1 + l + r := by
    rw [← F.L.image_indexSupport μ (LongPadded.earlier π m),
      Finset.card_image_of_injective _ F.L.injective]
    simpa only [l, r, PartnerFrame.cap, Bool.false_eq_true, ↓reduceIte] using
      SupportCaps.card_le (F.L.indexSupport μ (LongPadded.earlier π m)) F.t
  have h := BidirectionalGap.log_support_le_sub_losses
    (L := (L : ℝ)) (R := (R : ℝ)) (l := (l : ℝ)) (r := (r : ℝ))
    (X := (partnerSupportFinset I μ (LongPadded.earlier π m) m).card)
    (by positivity) (by positivity) (by exact_mod_cast hl) (by exact_mod_cast hr)
    (by exact_mod_cast hμ.support_card_pos (LongPadded.earlier π m) m) (by exact_mod_cast hcard)
  have hgap : (Gap.size (F.longSeen π) (LongPadded.position F.t) : ℝ) =
      1 + (L : ℝ) + R := by
    exact_mod_cast Gap.size_eq_one_add_sides (F.longSeen π) (LongPadded.position F.t)
  have hf : (F.longDirectional hμ false).loss π =
      Real.log (1 + (L : ℝ) + R) - Real.log (1 + (l : ℝ) + R) := by
    change Real.log (1 + (R : ℝ) + L) - Real.log (1 + (R : ℝ) + l) = _
    congr 1 <;> congr 1 <;> ring
  have ht : (F.longDirectional hμ true).loss π =
      Real.log (1 + (L : ℝ) + R) - Real.log (1 + (L : ℝ) + r) := rfl
  rw [hgap, hf, ht]
  exact h

theorem PartnerFrame.average_log_support_le_long_savings (F : PartnerFrame I μ m)
    (hμ : Stable I μ) {N : ℕ} (hN : 0 < N) :
    average (fun π => Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card) ≤
      refinedLogBound N - F.longMeanSaving hμ false - F.longMeanSaving hμ true := by
  classical
  have h := average_mono (F.log_support_le_long_losses hμ)
  rw [average_sub, average_sub] at h
  have hg := Gap.average_log_size_le_refinedLogBound F.longOwner
    F.longOwner_injective (LongPadded.position F.t) hN
  change average (fun π => Real.log (Gap.size (F.longSeen π) (LongPadded.position F.t))) ≤
    refinedLogBound N at hg
  change average (fun π => Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card) ≤
    average (fun π => Real.log (Gap.size (F.longSeen π) (LongPadded.position F.t))) -
      F.longMeanSaving hμ false - F.longMeanSaving hμ true at h
  linarith

theorem average_sum_log_support_le_long_events (hμ : Stable I μ) {N : ℕ} (hN : 0 < N) :
    average (fun π => ∑ m,
      Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card) ≤
      n * (refinedLogBound N - 2 * LongerLogCertificate.saving) := by
  classical
  let F := partnerFrame hμ
  have hl := sum_long_directional_savings hμ F false
  have hr := sum_long_directional_savings hμ F true
  rw [average_finset_sum]
  calc
    _ ≤ ∑ m, (refinedLogBound N - (F m).longMeanSaving hμ false - (F m).longMeanSaving hμ true) :=
      Finset.sum_le_sum (fun m _ => (F m).average_log_support_le_long_savings hμ hN)
    _ = n * refinedLogBound N - (∑ m, (F m).longMeanSaving hμ false) -
        (∑ m, (F m).longMeanSaving hμ true) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp
    _ ≤ _ := by nlinarith

theorem stableCount_le_exp_longerLogBound (I : Profile n) {N : ℕ} (hN : 0 < N) :
    (stableCount I : ℝ) ≤
      Real.exp (n * (refinedLogBound N - 2 * LongerLogCertificate.saving)) := by
  apply stableCount_le_exp_of_average_rank_sum I
    (fun (π : Equiv.Perm (Fin (n + 48))) u => π (LongPadded.realLabel u))
    (fun π => π.injective.comp LongPadded.realLabel_injective)
  intro μ hμ
  exact average_sum_log_support_le_long_events hμ hN

/-- Every complete strict balanced instance has fewer than 3.18^n stable matchings. -/
theorem stableCount_lt_318_pow (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (159 / 50 : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ Real.exp (n * (refinedLogBound 512 - 2 * LongerLogCertificate.saving)) :=
      stableCount_le_exp_longerLogBound I (by norm_num)
    _ < Real.exp (n * Real.log (159 / 50 : ℝ)) := Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left
        LongerLogCertificate.refinedLogBound_sub_two_savings_lt_log hnR)
    _ = _ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 159 / 50)]

end SmpMax.General

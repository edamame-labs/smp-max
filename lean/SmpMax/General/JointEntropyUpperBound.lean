import SmpMax.General.JointMatchingSaving

/-!
# The unconditional general 3.178 upper bound

The common-gap entropy cost includes the positive joint remainder as well
as the two directional losses. The strengthened charging theorem retains
a uniform joint saving after summing over the real matching coordinates.
-/

namespace SmpMax.General

open FiniteProbability LongerLogCertificate JointLogCertificate

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

set_option maxHeartbeats 1000000 in
-- Unfolding the padded directional interfaces requires the larger elaboration budget.
theorem PartnerFrame.log_support_le_joint_losses (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (π : Equiv.Perm (Fin (n + 48))) :
    Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card ≤
      Real.log (Gap.size (F.longSeen π) (LongPadded.position F.t)) -
        (F.longDirectional hμ false).loss π - (F.longDirectional hμ true).loss π -
        F.jointLoss π := by
  let L := Gap.leftSize (F.longSeen π) (LongPadded.position F.t)
  let R := Gap.rightSize (F.longSeen π) (LongPadded.position F.t)
  let l := F.cap false (LongPadded.earlier π m)
  let r := F.cap true (LongPadded.earlier π m)
  have hcard : (partnerSupportFinset I μ (LongPadded.earlier π m) m).card ≤ 1 + l + r := by
    rw [← F.L.image_indexSupport μ (LongPadded.earlier π m),
      Finset.card_image_of_injective _ F.L.injective]
    simpa only [l, r, PartnerFrame.cap, Bool.false_eq_true, ↓reduceIte] using
      SupportCaps.card_le (F.L.indexSupport μ (LongPadded.earlier π m)) F.t
  have hcardR : ((partnerSupportFinset I μ (LongPadded.earlier π m) m).card : ℝ) ≤
      1 + (l : ℝ) + r := by exact_mod_cast hcard
  have h := Real.log_le_log
    (by exact_mod_cast hμ.support_card_pos (LongPadded.earlier π m) m) hcardR
  have hgap : (Gap.size (F.longSeen π) (LongPadded.position F.t) : ℝ) =
      1 + (L : ℝ) + R := by
    exact_mod_cast Gap.size_eq_one_add_sides (F.longSeen π) (LongPadded.position F.t)
  have hf : (F.longDirectional hμ false).loss π =
      Real.log (1 + (L : ℝ) + R) - Real.log (1 + (l : ℝ) + R) := by
    change Real.log (1 + (R : ℝ) + L) - Real.log (1 + (R : ℝ) + l) = _
    congr 1 <;> congr 1 <;> ring
  have ht : (F.longDirectional hμ true).loss π =
      Real.log (1 + (L : ℝ) + R) - Real.log (1 + (L : ℝ) + r) := rfl
  have hj : F.jointLoss π = JointGap.loss L R l r := rfl
  rw [hgap, hf, ht, hj]
  unfold JointGap.loss
  linarith

theorem PartnerFrame.average_log_support_le_combined (F : PartnerFrame I μ m)
    (hμ : Stable I μ) {N : ℕ} (hN : 0 < N) :
    average (fun π => Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card) ≤
      refinedLogBound N - F.combinedMeanSaving hμ := by
  classical
  have h := average_mono (F.log_support_le_joint_losses hμ)
  rw [average_sub, average_sub, average_sub] at h
  have hg := Gap.average_log_size_le_refinedLogBound F.longOwner
    F.longOwner_injective (LongPadded.position F.t) hN
  change average (fun π => Real.log (Gap.size (F.longSeen π) (LongPadded.position F.t))) ≤
    refinedLogBound N at hg
  change average (fun π => Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card) ≤
    average (fun π => Real.log (Gap.size (F.longSeen π) (LongPadded.position F.t))) -
      F.longMeanSaving hμ false - F.longMeanSaving hμ true - average F.jointLoss at h
  unfold combinedMeanSaving
  linarith

theorem average_sum_log_support_le_joint (hμ : Stable I μ) {N : ℕ} (hN : 0 < N) :
    average (fun π => ∑ m,
      Real.log (partnerSupportFinset I μ (LongPadded.earlier π m) m).card) ≤
      n * (refinedLogBound N - 2 * saving - jointSaving) := by
  classical
  let F := partnerFrame hμ
  have hs := sum_combined_savings hμ F
  rw [average_finset_sum]
  calc
    _ ≤ ∑ m, (refinedLogBound N - (F m).combinedMeanSaving hμ) :=
      Finset.sum_le_sum (fun m _ => (F m).average_log_support_le_combined hμ hN)
    _ = n * refinedLogBound N - ∑ m, (F m).combinedMeanSaving hμ := by
      rw [Finset.sum_sub_distrib]
      simp
    _ ≤ _ := by nlinarith

theorem stableCount_le_exp_jointLogBound (I : Profile n) {N : ℕ} (hN : 0 < N) :
    (stableCount I : ℝ) ≤ Real.exp (n * (refinedLogBound N - 2 * saving - jointSaving)) := by
  apply stableCount_le_exp_of_average_rank_sum I
    (fun (π : Equiv.Perm (Fin (n + 48))) u => π (LongPadded.realLabel u))
    (fun π => π.injective.comp LongPadded.realLabel_injective)
  intro μ hμ
  exact average_sum_log_support_le_joint hμ hN

/-- Every complete strict balanced instance has fewer than 3.178^n stable matchings. -/
theorem stableCount_lt_3178_pow (hn : 0 < n) (I : Profile n) :
    (stableCount I : ℝ) < (1589 / 500 : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ Real.exp (n * (refinedLogBound 512 - 2 * saving - jointSaving)) :=
      stableCount_le_exp_jointLogBound I (by norm_num)
    _ < Real.exp (n * Real.log (1589 / 500 : ℝ)) := Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left refinedLogBound_sub_savings_lt_log hnR)
    _ = _ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 1589 / 500)]

end SmpMax.General

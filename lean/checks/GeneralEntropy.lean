import SmpMax.General.PartnerIntervals
import SmpMax.General.MatchingRevelation
import SmpMax.General.EntropyUpperBound
import SmpMax.General.RefinedEntropyUpperBound
import SmpMax.General.SuccessorPropagation
import SmpMax.General.SuccessorCharging
import SmpMax.General.StructuralLogCertificate
import SmpMax.General.BidirectionalPropagation
import SmpMax.General.BidirectionalGapSaving
import SmpMax.General.BidirectionalLogCertificate
import SmpMax.General.BidirectionalEntropyUpperBound
import SmpMax.General.LongerEntropyUpperBound
import SmpMax.General.JointEntropyUpperBound

/-!
Review the actual theorem signatures and their axiom dependencies.
This audit covers the complete unconditional 3.178 counting theorem, its
finite event and matching-level components, and the preserved earlier bounds.
-/

#check @SmpMax.General.stable_pair_separation
#check @SmpMax.General.compatible_same_side
#check @SmpMax.General.PartnerOrder.support_card_le_gap
#check @SmpMax.General.PartnerOrder.owners_injective
#check @SmpMax.General.Revelation.count_le_sum_cost
#check @SmpMax.General.stableCount_mul_log_le_sum_supportCost
#check @SmpMax.General.PartnerOrder.support_card_le_revelationGap
#check @SmpMax.General.Gap.size_ge_iff_window
#check @SmpMax.General.PermutationCounting.card_mul_first_two
#check @SmpMax.General.Gap.long_gap_cover
#check @SmpMax.General.Gap.probability_size_ge_le
#check @SmpMax.General.FiniteProbability.average_log_eq_tail_sum
#check @SmpMax.General.Gap.average_log_size_le_finiteLogBound
#check @SmpMax.General.stableCount_le_exp_finiteLogBound
#check @SmpMax.General.LogCertificate.finiteLogBound_512_lt_log
#check @SmpMax.General.stableCount_lt_3332_pow
#check @SmpMax.General.gapTerm_le_refined_difference
#check @SmpMax.General.Gap.average_log_size_le_refinedLogBound
#check @SmpMax.General.RefinedLogCertificate.refinedLogBound_512_lt_log
#check @SmpMax.General.stableCount_le_exp_of_average_log_support
#check @SmpMax.General.stableCount_le_exp_refinedLogBound
#check @SmpMax.General.stableCount_lt_3331974_pow

#print axioms SmpMax.General.stable_pair_separation
#print axioms SmpMax.General.compatible_same_side
#print axioms SmpMax.General.PartnerOrder.support_card_le_gap
#print axioms SmpMax.General.PartnerOrder.owners_injective
#print axioms SmpMax.General.Revelation.count_le_sum_cost
#print axioms SmpMax.General.stableCount_mul_log_le_sum_supportCost
#print axioms SmpMax.General.PartnerOrder.support_card_le_revelationGap
#print axioms SmpMax.General.Gap.size_ge_iff_window
#print axioms SmpMax.General.PermutationCounting.card_mul_first_two
#print axioms SmpMax.General.Gap.long_gap_cover
#print axioms SmpMax.General.Gap.probability_size_ge_le
#print axioms SmpMax.General.FiniteProbability.average_log_eq_tail_sum
#print axioms SmpMax.General.Gap.average_log_size_le_finiteLogBound
#print axioms SmpMax.General.stableCount_le_exp_finiteLogBound
#print axioms SmpMax.General.LogCertificate.finiteLogBound_512_lt_log
#print axioms SmpMax.General.stableCount_lt_3332_pow
#print axioms SmpMax.General.gapTerm_le_refined_difference
#print axioms SmpMax.General.Gap.average_log_size_le_refinedLogBound
#print axioms SmpMax.General.RefinedLogCertificate.refinedLogBound_512_lt_log
#print axioms SmpMax.General.stableCount_le_exp_of_average_log_support
#print axioms SmpMax.General.stableCount_le_exp_refinedLogBound
#print axioms SmpMax.General.stableCount_lt_3331974_pow

#check @SmpMax.General.crossing_forces_owner_worse
#check @SmpMax.General.worsening_propagates
#check @SmpMax.General.compatible_successor_upper_barrier
#check @SmpMax.General.SuccessorCharging.card_exceptions_le_twice_noncycles
#check @SmpMax.General.SuccessorCharging.sum_saving_ge
#check @SmpMax.General.Gap.probability_size_ge_le_short
#check @SmpMax.General.Gap.average_log_size_le_refined_sub_short
#check @SmpMax.General.StructuralLogCertificate.shortSideSaving_ge_three
#check @SmpMax.General.StructuralLogCertificate.second_step_saving_eq
#check @SmpMax.General.StructuralLogCertificate.rational_power_comparison
#check @SmpMax.General.StructuralLogCertificate.refinedLogBound_sub_saving_lt_log

#print axioms SmpMax.General.crossing_forces_owner_worse
#print axioms SmpMax.General.worsening_propagates
#print axioms SmpMax.General.compatible_successor_upper_barrier
#print axioms SmpMax.General.SuccessorCharging.card_exceptions_le_twice_noncycles
#print axioms SmpMax.General.SuccessorCharging.sum_saving_ge
#print axioms SmpMax.General.Gap.probability_size_ge_le_short
#print axioms SmpMax.General.Gap.average_log_size_le_refined_sub_short
#print axioms SmpMax.General.StructuralLogCertificate.shortSideSaving_ge_three
#print axioms SmpMax.General.StructuralLogCertificate.second_step_saving_eq
#print axioms SmpMax.General.StructuralLogCertificate.rational_power_comparison
#print axioms SmpMax.General.StructuralLogCertificate.refinedLogBound_sub_saving_lt_log

#check @SmpMax.General.crossing_forces_owner_better
#check @SmpMax.General.improving_propagates
#check @SmpMax.General.compatible_predecessor_lower_barrier
#check @SmpMax.General.BidirectionalGap.log_caps_superadditive
#check @SmpMax.General.BidirectionalGap.log_support_le_sub_losses
#check @SmpMax.General.BidirectionalGap.directional_loss_ge
#check @SmpMax.General.BidirectionalLogCertificate.shortSideSaving_ge_three
#check @SmpMax.General.BidirectionalLogCertificate.firstStepSaving_ge_three
#check @SmpMax.General.BidirectionalLogCertificate.secondStepSaving_eq
#check @SmpMax.General.BidirectionalLogCertificate.firstStepSaving_le_first_coincidence
#check @SmpMax.General.BidirectionalLogCertificate.saving_le_first_coincidence
#check @SmpMax.General.BidirectionalLogCertificate.saving_le_second_coincidence
#check @SmpMax.General.BidirectionalLogCertificate.saving_le_third_coincidence
#check @SmpMax.General.BidirectionalLogCertificate.rational_power_comparison
#check @SmpMax.General.BidirectionalLogCertificate.refinedLogBound_sub_two_savings_lt_log

#print axioms SmpMax.General.crossing_forces_owner_better
#print axioms SmpMax.General.improving_propagates
#print axioms SmpMax.General.compatible_predecessor_lower_barrier
#print axioms SmpMax.General.BidirectionalGap.log_caps_superadditive
#print axioms SmpMax.General.BidirectionalGap.log_support_le_sub_losses
#print axioms SmpMax.General.BidirectionalGap.directional_loss_ge
#print axioms SmpMax.General.BidirectionalLogCertificate.shortSideSaving_ge_three
#print axioms SmpMax.General.BidirectionalLogCertificate.firstStepSaving_ge_three
#print axioms SmpMax.General.BidirectionalLogCertificate.secondStepSaving_eq
#print axioms SmpMax.General.BidirectionalLogCertificate.firstStepSaving_le_first_coincidence
#print axioms SmpMax.General.BidirectionalLogCertificate.saving_le_first_coincidence
#print axioms SmpMax.General.BidirectionalLogCertificate.saving_le_second_coincidence
#print axioms SmpMax.General.BidirectionalLogCertificate.saving_le_third_coincidence
#print axioms SmpMax.General.BidirectionalLogCertificate.rational_power_comparison
#print axioms SmpMax.General.BidirectionalLogCertificate.refinedLogBound_sub_two_savings_lt_log

#check @SmpMax.General.PermutationCounting.card_mul_first_three
#print axioms SmpMax.General.PermutationCounting.card_mul_first_three
#check @SmpMax.General.PermutationCounting.probability_beforeOne
#print axioms SmpMax.General.PermutationCounting.probability_beforeOne
#check @SmpMax.General.PermutationCounting.probability_beforeTwo
#print axioms SmpMax.General.PermutationCounting.probability_beforeTwo
#check @SmpMax.General.stableCount_le_exp_of_average_rank_sum
#print axioms SmpMax.General.stableCount_le_exp_of_average_rank_sum
#check @SmpMax.General.FiniteProbability.disjoint_events_average
#print axioms SmpMax.General.FiniteProbability.disjoint_events_average
#check @SmpMax.General.LocalGap.probability_twoEvent
#print axioms SmpMax.General.LocalGap.probability_twoEvent
#check @SmpMax.General.LocalGap.DirectionalData.short_saving
#print axioms SmpMax.General.LocalGap.DirectionalData.short_saving
#check @SmpMax.General.LocalGap.DirectionalData.first_step_saving
#print axioms SmpMax.General.LocalGap.DirectionalData.first_step_saving
#check @SmpMax.General.LocalGap.DirectionalData.second_step_saving
#print axioms SmpMax.General.LocalGap.DirectionalData.second_step_saving
#check @SmpMax.General.LocalGap.event_lengths
#print axioms SmpMax.General.LocalGap.event_lengths
#check @SmpMax.General.Padded.owner_injective
#print axioms SmpMax.General.Padded.owner_injective
#check @SmpMax.General.SupportCaps.card_le
#print axioms SmpMax.General.SupportCaps.card_le
#check @SmpMax.General.PartnerFrame.directionOwner_eq_neighbor
#print axioms SmpMax.General.PartnerFrame.directionOwner_eq_neighbor
#check @SmpMax.General.PartnerFrame.neighborOwner_active
#print axioms SmpMax.General.PartnerFrame.neighborOwner_active
#check @SmpMax.General.PartnerFrame.cap_le_of_propagated
#print axioms SmpMax.General.PartnerFrame.cap_le_of_propagated
#check @SmpMax.General.PartnerFrame.support_between_padded
#print axioms SmpMax.General.PartnerFrame.support_between_padded
#check @SmpMax.General.PartnerFrame.cap_le_padded
#print axioms SmpMax.General.PartnerFrame.cap_le_padded
#check @SmpMax.General.PartnerFrame.meanSaving_first
#print axioms SmpMax.General.PartnerFrame.meanSaving_first
#check @SmpMax.General.PartnerFrame.meanSaving_second
#print axioms SmpMax.General.PartnerFrame.meanSaving_second
#check @SmpMax.General.sum_directional_savings
#print axioms SmpMax.General.sum_directional_savings
#check @SmpMax.General.PartnerFrame.log_support_le_two_losses
#print axioms SmpMax.General.PartnerFrame.log_support_le_two_losses
#check @SmpMax.General.average_sum_log_support_le_bidirectional
#print axioms SmpMax.General.average_sum_log_support_le_bidirectional
#check @SmpMax.General.stableCount_le_exp_bidirectionalLogBound
#print axioms SmpMax.General.stableCount_le_exp_bidirectionalLogBound
#check @SmpMax.General.stableCount_lt_32_pow
#print axioms SmpMax.General.stableCount_lt_32_pow

-- Pin the complete public statement, including every hypothesis.
example : ∀ n : ℕ, 0 < n → ∀ I : SmpMax.General.Profile n,
    (SmpMax.General.stableCount I : ℝ) < (16 / 5 : ℝ) ^ n :=
  fun _n hn I => SmpMax.General.stableCount_lt_32_pow hn I

#check @SmpMax.General.LongerLogCertificate.incrementFloor_le
#print axioms SmpMax.General.LongerLogCertificate.incrementFloor_le
#check @SmpMax.General.LongerLogCertificate.row_saving_ge
#print axioms SmpMax.General.LongerLogCertificate.row_saving_ge
#check @SmpMax.General.LongerLogCertificate.shortSaving_ge_three
#print axioms SmpMax.General.LongerLogCertificate.shortSaving_ge_three
#check @SmpMax.General.LongerLogCertificate.firstSaving_ge_three
#print axioms SmpMax.General.LongerLogCertificate.firstSaving_ge_three
#check @SmpMax.General.LongerLogCertificate.refinedLogBound_sub_two_savings_lt_log
#print axioms SmpMax.General.LongerLogCertificate.refinedLogBound_sub_two_savings_lt_log
#check @SmpMax.General.LongGap.probability_twoEvent
#print axioms SmpMax.General.LongGap.probability_twoEvent
#check @SmpMax.General.LongGap.exists_second_row
#print axioms SmpMax.General.LongGap.exists_second_row
#check @SmpMax.General.LongGap.DirectionalData.short_saving
#print axioms SmpMax.General.LongGap.DirectionalData.short_saving
#check @SmpMax.General.LongGap.DirectionalData.first_step_saving
#print axioms SmpMax.General.LongGap.DirectionalData.first_step_saving
#check @SmpMax.General.LongGap.DirectionalData.second_step_saving
#print axioms SmpMax.General.LongGap.DirectionalData.second_step_saving
#check @SmpMax.General.LongGap.event_lengths
#print axioms SmpMax.General.LongGap.event_lengths
#check @SmpMax.General.LongPadded.owner_injective
#print axioms SmpMax.General.LongPadded.owner_injective
#check @SmpMax.General.PartnerFrame.support_between_long_gap
#print axioms SmpMax.General.PartnerFrame.support_between_long_gap
#check @SmpMax.General.PartnerFrame.cap_le_long_gap
#print axioms SmpMax.General.PartnerFrame.cap_le_long_gap
#check @SmpMax.General.PartnerFrame.longMeanSaving_first
#print axioms SmpMax.General.PartnerFrame.longMeanSaving_first
#check @SmpMax.General.PartnerFrame.longMeanSaving_second
#print axioms SmpMax.General.PartnerFrame.longMeanSaving_second
#check @SmpMax.General.sum_long_directional_savings
#print axioms SmpMax.General.sum_long_directional_savings
#check @SmpMax.General.PartnerFrame.log_support_le_long_losses
#print axioms SmpMax.General.PartnerFrame.log_support_le_long_losses
#check @SmpMax.General.average_sum_log_support_le_long_events
#print axioms SmpMax.General.average_sum_log_support_le_long_events
#check @SmpMax.General.stableCount_le_exp_longerLogBound
#print axioms SmpMax.General.stableCount_le_exp_longerLogBound
#check @SmpMax.General.stableCount_lt_318_pow
#print axioms SmpMax.General.stableCount_lt_318_pow

-- Pin the stronger statement with the unchanged profile and count definitions.
example : ∀ n : ℕ, 0 < n → ∀ I : SmpMax.General.Profile n,
    (SmpMax.General.stableCount I : ℝ) < (159 / 50 : ℝ) ^ n :=
  fun _n hn I => SmpMax.General.stableCount_lt_318_pow hn I

#check @SmpMax.General.JointGap.loss_nonneg
#print axioms SmpMax.General.JointGap.loss_nonneg

#check @SmpMax.General.JointGap.loss_ge
#print axioms SmpMax.General.JointGap.loss_ge

#check @SmpMax.General.JointLogCertificate.jointSaving_le
#print axioms SmpMax.General.JointLogCertificate.jointSaving_le

#check @SmpMax.General.JointLogCertificate.short_ge
#print axioms SmpMax.General.JointLogCertificate.short_ge

#check @SmpMax.General.JointLogCertificate.first_outside_ge
#print axioms SmpMax.General.JointLogCertificate.first_outside_ge

#check @SmpMax.General.JointLogCertificate.refinedLogBound_sub_savings_lt_log
#print axioms SmpMax.General.JointLogCertificate.refinedLogBound_sub_savings_lt_log

#check @SmpMax.General.LongGap.DirectionalData.first_step_joint_saving
#print axioms SmpMax.General.LongGap.DirectionalData.first_step_joint_saving

#check @SmpMax.General.LongGap.DirectionalData.second_step_collision_saving
#print axioms SmpMax.General.LongGap.DirectionalData.second_step_collision_saving

#check @SmpMax.General.LongGap.cut_side_ge_two
#print axioms SmpMax.General.LongGap.cut_side_ge_two

#check @SmpMax.General.LongGap.joint_probability_ge
#print axioms SmpMax.General.LongGap.joint_probability_ge

#check @SmpMax.General.PartnerFrame.jointMeanSaving_ge
#print axioms SmpMax.General.PartnerFrame.jointMeanSaving_ge

#check @SmpMax.General.PartnerFrame.combinedMeanSaving_regular
#print axioms SmpMax.General.PartnerFrame.combinedMeanSaving_regular

#check @SmpMax.General.SuccessorCharging.sum_joint_saving_ge
#print axioms SmpMax.General.SuccessorCharging.sum_joint_saving_ge

#check @SmpMax.General.PartnerFrame.second_joint_witness
#print axioms SmpMax.General.PartnerFrame.second_joint_witness

#check @SmpMax.General.sum_combined_savings
#print axioms SmpMax.General.sum_combined_savings

#check @SmpMax.General.PartnerFrame.log_support_le_joint_losses
#print axioms SmpMax.General.PartnerFrame.log_support_le_joint_losses

#check @SmpMax.General.average_sum_log_support_le_joint
#print axioms SmpMax.General.average_sum_log_support_le_joint

#check @SmpMax.General.stableCount_le_exp_jointLogBound
#print axioms SmpMax.General.stableCount_le_exp_jointLogBound

#check @SmpMax.General.stableCount_lt_3178_pow
#print axioms SmpMax.General.stableCount_lt_3178_pow

-- Pin the joint-saving theorem with every hypothesis explicit.
example : ∀ n : ℕ, 0 < n → ∀ I : SmpMax.General.Profile n,
    (SmpMax.General.stableCount I : ℝ) < (1589 / 500 : ℝ) ^ n :=
  fun _n hn I => SmpMax.General.stableCount_lt_3178_pow hn I

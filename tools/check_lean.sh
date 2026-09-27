#!/usr/bin/env bash
# Build the formal development and check the existing trust boundary.
set -euo pipefail
SMP_REPO=$(cd "$(dirname "$0")/.." && pwd)
cd "$SMP_REPO/lean"
lake build SmpMax export_cnf export_sched_cnf export_cubes6
if grep -rnE '\bsorry\b' SmpMax; then
  echo 'Unexpected sorry in the Lean library' >&2
  exit 1
fi
SMP_CHECK_DIR=$(mktemp -d)
trap 'rm -rf "$SMP_CHECK_DIR"' EXIT
cat > "$SMP_CHECK_DIR/axioms.lean" <<'LEAN'
import SmpMax
#print axioms f5_eq_16_of_unsat
#print axioms bridge
#print axioms chain_complete
#print axioms traj_mem_iff
#print axioms wtraj_nodup
#print axioms total_moves_le_30
#print axioms count_le_of_orderPreserving
#print axioms sc_le_readoffS_chainSched
#print axioms manOpt_wrelabel6
#print axioms validity_unconditional
#print axioms PM_sem
#print axioms PW_sem
#print axioms Legal_length_le_15
#print axioms minFirst_mem_cyclicShapes
#print axioms permsN6_perm_permutations
#print axioms Legal_map_minFirst
#print axioms SchedCNF6.dec_pwVar3
#print axioms firstApp_relabel
#print axioms Legal_relabel
#print axioms sc_le_readoffS_relabelSched
#print axioms exists_canonical_schedule
#print axioms fits_final
#print axioms cube_faithful6
#print axioms dihedral6_count
#print axioms f6_upper_of_unsat
#print axioms f6_eq_48_of_unsat
LEAN
lake env lean "$SMP_CHECK_DIR/axioms.lean" | tee "$SMP_CHECK_DIR/axioms.txt"
python3 - "$SMP_CHECK_DIR/axioms.txt" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
matches=re.findall(r"depends on axioms: \[([^]]*)\]",text)
expected={'propext','Classical.choice','Quot.sound'}
if len(matches)!=26 or any(set(s.split(', '))!=expected for s in matches):
    sys.exit('Unexpected axiom dependency or missing theorem output')
PY
lake env lean checks/GeneralEntropy.lean | tee "$SMP_CHECK_DIR/general-axioms.txt"
python3 - "$SMP_CHECK_DIR/general-axioms.txt" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
expected_names={
    'SmpMax.General.stable_pair_separation',
    'SmpMax.General.compatible_same_side',
    'SmpMax.General.PartnerOrder.support_card_le_gap',
    'SmpMax.General.PartnerOrder.owners_injective',
    'SmpMax.General.Revelation.count_le_sum_cost',
    'SmpMax.General.stableCount_mul_log_le_sum_supportCost',
    'SmpMax.General.PartnerOrder.support_card_le_revelationGap',
    'SmpMax.General.Gap.size_ge_iff_window',
    'SmpMax.General.PermutationCounting.card_mul_first_two',
    'SmpMax.General.Gap.long_gap_cover',
    'SmpMax.General.Gap.probability_size_ge_le',
    'SmpMax.General.FiniteProbability.average_log_eq_tail_sum',
    'SmpMax.General.Gap.average_log_size_le_finiteLogBound',
    'SmpMax.General.stableCount_le_exp_finiteLogBound',
    'SmpMax.General.LogCertificate.finiteLogBound_512_lt_log',
    'SmpMax.General.stableCount_lt_3332_pow',
    'SmpMax.General.gapTerm_le_refined_difference',
    'SmpMax.General.Gap.average_log_size_le_refinedLogBound',
    'SmpMax.General.RefinedLogCertificate.refinedLogBound_512_lt_log',
    'SmpMax.General.stableCount_le_exp_of_average_log_support',
    'SmpMax.General.stableCount_le_exp_refinedLogBound',
    'SmpMax.General.stableCount_lt_3331974_pow',
    'SmpMax.General.crossing_forces_owner_worse',
    'SmpMax.General.worsening_propagates',
    'SmpMax.General.compatible_successor_upper_barrier',
    'SmpMax.General.SuccessorCharging.card_exceptions_le_twice_noncycles',
    'SmpMax.General.SuccessorCharging.sum_saving_ge',
    'SmpMax.General.Gap.probability_size_ge_le_short',
    'SmpMax.General.Gap.average_log_size_le_refined_sub_short',
    'SmpMax.General.StructuralLogCertificate.shortSideSaving_ge_three',
    'SmpMax.General.StructuralLogCertificate.second_step_saving_eq',
    'SmpMax.General.StructuralLogCertificate.rational_power_comparison',
    'SmpMax.General.StructuralLogCertificate.refinedLogBound_sub_saving_lt_log',
    'SmpMax.General.crossing_forces_owner_better',
    'SmpMax.General.improving_propagates',
    'SmpMax.General.compatible_predecessor_lower_barrier',
    'SmpMax.General.BidirectionalGap.log_caps_superadditive',
    'SmpMax.General.BidirectionalGap.log_support_le_sub_losses',
    'SmpMax.General.BidirectionalGap.directional_loss_ge',
    'SmpMax.General.BidirectionalLogCertificate.shortSideSaving_ge_three',
    'SmpMax.General.BidirectionalLogCertificate.firstStepSaving_ge_three',
    'SmpMax.General.BidirectionalLogCertificate.secondStepSaving_eq',
    'SmpMax.General.BidirectionalLogCertificate.firstStepSaving_le_first_coincidence',
    'SmpMax.General.BidirectionalLogCertificate.saving_le_first_coincidence',
    'SmpMax.General.BidirectionalLogCertificate.saving_le_second_coincidence',
    'SmpMax.General.BidirectionalLogCertificate.saving_le_third_coincidence',
    'SmpMax.General.BidirectionalLogCertificate.rational_power_comparison',
    'SmpMax.General.BidirectionalLogCertificate.refinedLogBound_sub_two_savings_lt_log',
    'SmpMax.General.PermutationCounting.card_mul_first_three',
    'SmpMax.General.PermutationCounting.probability_beforeOne',
    'SmpMax.General.PermutationCounting.probability_beforeTwo',
    'SmpMax.General.stableCount_le_exp_of_average_rank_sum',
    'SmpMax.General.FiniteProbability.disjoint_events_average',
    'SmpMax.General.LocalGap.probability_twoEvent',
    'SmpMax.General.LocalGap.DirectionalData.short_saving',
    'SmpMax.General.LocalGap.DirectionalData.first_step_saving',
    'SmpMax.General.LocalGap.DirectionalData.second_step_saving',
    'SmpMax.General.LocalGap.event_lengths',
    'SmpMax.General.Padded.owner_injective',
    'SmpMax.General.SupportCaps.card_le',
    'SmpMax.General.PartnerFrame.directionOwner_eq_neighbor',
    'SmpMax.General.PartnerFrame.neighborOwner_active',
    'SmpMax.General.PartnerFrame.cap_le_of_propagated',
    'SmpMax.General.PartnerFrame.support_between_padded',
    'SmpMax.General.PartnerFrame.cap_le_padded',
    'SmpMax.General.PartnerFrame.meanSaving_first',
    'SmpMax.General.PartnerFrame.meanSaving_second',
    'SmpMax.General.sum_directional_savings',
    'SmpMax.General.PartnerFrame.log_support_le_two_losses',
    'SmpMax.General.average_sum_log_support_le_bidirectional',
    'SmpMax.General.stableCount_le_exp_bidirectionalLogBound',
    'SmpMax.General.stableCount_lt_32_pow',
    'SmpMax.General.LongerLogCertificate.incrementFloor_le',
    'SmpMax.General.LongerLogCertificate.row_saving_ge',
    'SmpMax.General.LongerLogCertificate.shortSaving_ge_three',
    'SmpMax.General.LongerLogCertificate.firstSaving_ge_three',
    'SmpMax.General.LongerLogCertificate.refinedLogBound_sub_two_savings_lt_log',
    'SmpMax.General.LongGap.probability_twoEvent',
    'SmpMax.General.LongGap.exists_second_row',
    'SmpMax.General.LongGap.DirectionalData.short_saving',
    'SmpMax.General.LongGap.DirectionalData.first_step_saving',
    'SmpMax.General.LongGap.DirectionalData.second_step_saving',
    'SmpMax.General.LongGap.event_lengths',
    'SmpMax.General.LongPadded.owner_injective',
    'SmpMax.General.PartnerFrame.support_between_long_gap',
    'SmpMax.General.PartnerFrame.cap_le_long_gap',
    'SmpMax.General.PartnerFrame.longMeanSaving_first',
    'SmpMax.General.PartnerFrame.longMeanSaving_second',
    'SmpMax.General.sum_long_directional_savings',
    'SmpMax.General.PartnerFrame.log_support_le_long_losses',
    'SmpMax.General.average_sum_log_support_le_long_events',
    'SmpMax.General.stableCount_le_exp_longerLogBound',
    'SmpMax.General.stableCount_lt_318_pow',
    'SmpMax.General.JointGap.loss_nonneg',
    'SmpMax.General.JointGap.loss_ge',
    'SmpMax.General.JointLogCertificate.jointSaving_le',
    'SmpMax.General.JointLogCertificate.short_ge',
    'SmpMax.General.JointLogCertificate.first_outside_ge',
    'SmpMax.General.JointLogCertificate.refinedLogBound_sub_savings_lt_log',
    'SmpMax.General.LongGap.DirectionalData.first_step_joint_saving',
    'SmpMax.General.LongGap.DirectionalData.second_step_collision_saving',
    'SmpMax.General.LongGap.cut_side_ge_two',
    'SmpMax.General.LongGap.joint_probability_ge',
    'SmpMax.General.PartnerFrame.jointMeanSaving_ge',
    'SmpMax.General.PartnerFrame.combinedMeanSaving_regular',
    'SmpMax.General.SuccessorCharging.sum_joint_saving_ge',
    'SmpMax.General.PartnerFrame.second_joint_witness',
    'SmpMax.General.sum_combined_savings',
    'SmpMax.General.PartnerFrame.log_support_le_joint_losses',
    'SmpMax.General.average_sum_log_support_le_joint',
    'SmpMax.General.stableCount_le_exp_jointLogBound',
    'SmpMax.General.stableCount_lt_3178_pow',
}
matches=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
allowed={'propext','Classical.choice','Quot.sound'}
if len(matches)!=len(expected_names) or {name for name,_ in matches}!=expected_names:
    sys.exit('Missing or duplicate general theorem audit output')
if any(not set(filter(None, re.split(r',\s*', deps.strip()))) <= allowed for _,deps in matches):
    sys.exit('Unexpected axiom dependency in a general theorem')
PY
lake env lean checks/FiveWitness.lean | tee "$SMP_CHECK_DIR/witness.txt"
grep -q 'depends on axioms: \[propext\]' "$SMP_CHECK_DIR/witness.txt"
lake env lean SmpMax/Checks/FiveCountCrossCheck.lean | tee "$SMP_CHECK_DIR/cross-check.txt"
grep -q 'mismatches: 0' "$SMP_CHECK_DIR/cross-check.txt"
lake env lean SmpMax/Checks/FourLratPilot.lean
echo 'Lean build, axiom checks, standalone witness, differential count, and LRAT pilot passed.'

import SmpMax.General.LongDirectionalSaving
import SmpMax.General.JointLogCertificate

/-!
# Stronger noncycle savings and cross-direction collision margins

Three first-step events cover the extra charging cost. A second-step
witness at either of the first two opposite positions already supplies
the joint margin through its larger individual saving.
-/

namespace SmpMax.General.LongGap

open FiniteProbability LongerLogCertificate JointLogCertificate

variable {N : ℕ}

theorem DirectionalData.first_step_joint_saving (D : DirectionalData N) (u : Fin N)
    (hu0 : u ≠ D.label 0) (hu1 : u ≠ D.label 1)
    (hcap : ∀ π, π u < π (D.label 0) → D.cap π ≤ 0) :
    3 * (saving + jointSaving) ≤ average D.loss := by
  classical
  have h := D.propagation_events u (q := 0) (J := 3) (by omega) (by omega) hcap
  simp only [Fin.sum_univ_three, Nat.add_zero, Fin.val_zero, Fin.val_one, Fin.val_two] at h
  have ha21 : afterLabels D.label 2 1 = {D.label 1, D.label 25, D.label 26} := by
    have ha : afterIndices 2 1 = {1, 25, 26} := by decide
    simp [afterLabels, ha]
  have hp0 := probability_twoEvent D.label D.injective u hu0
    (by omega : 0 ≤ 23) (by omega : 1 ≤ 3)
  have hp1 := probability_twoEvent D.label D.injective u hu0
    (by omega : 1 ≤ 23) (by omega : 1 ≤ 3)
  have hp2 := probability_twoEvent D.label D.injective u hu0
    (by omega : 2 ≤ 23) (by omega : 1 ≤ 3)
  simp only [afterLabels_01, afterLabels_11, ha21, Finset.mem_singleton,
    Finset.mem_insert, hu1, false_or, boundary_zero, boundary_one, boundary_two] at hp0 hp1 hp2
  by_cases h25 : u = D.label 25
  · subst u
    norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1 hp2
    rw [hp0, hp1, hp2] at h
    have hc := first_zero_ge
    linarith
  · by_cases h26 : u = D.label 26
    · subst u
      norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1 hp2
      rw [hp0, hp1, hp2] at h
      have hc := first_one_ge
      linarith
    · by_cases h27 : u = D.label 27
      · subst u
        norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1 hp2
        rw [hp0, hp1, hp2] at h
        have hc := first_outside_ge
        have hn := logIncrement_nonneg 2
        linarith
      · simp only [h25, h26, h27, false_or, ↓reduceIte] at hp0 hp1 hp2
        norm_num at hp0 hp1 hp2
        rw [hp0, hp1, hp2] at h
        have hc := first_outside_ge
        linarith

theorem DirectionalData.second_step_collision_saving (D : DirectionalData N) (u : Fin N)
    (hu0 : u ≠ D.label 0) (hu1 : u ≠ D.label 1) (hu2 : u ≠ D.label 2)
    (hcollision : u = D.label 25 ∨ u = D.label 26)
    (hcap : ∀ π, π u < π (D.label 0) → D.cap π ≤ 1) :
    saving + jointSaving ≤ average D.loss := by
  classical
  have h := D.propagation_events u (q := 1) (J := 2) (by omega) (by omega) hcap
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.reduceAdd] at h
  have hp0 := probability_twoEvent D.label D.injective u hu0
    (by omega : 0 ≤ 23) (by omega : 2 ≤ 3)
  have hp1 := probability_twoEvent D.label D.injective u hu0
    (by omega : 1 ≤ 23) (by omega : 2 ≤ 3)
  simp only [afterLabels_02, afterLabels_12, Finset.mem_singleton,
    Finset.mem_insert, hu1, hu2, false_or, boundary_zero, boundary_one] at hp0 hp1
  rcases hcollision with rfl | rfl
  · norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1
    rw [hp0, hp1] at h
    have hc := second_zero_ge
    linarith
  · norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1
    rw [hp0, hp1] at h
    have hc := second_one_ge
    linarith

end SmpMax.General.LongGap

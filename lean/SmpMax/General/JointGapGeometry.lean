import SmpMax.General.LongMatchingDirectionalSaving
import SmpMax.General.JointGapSaving
import SmpMax.General.JointDirectionalSaving

/-!
# A joint saving on the actual padded partner gap

Two earlier witnesses and four later neighbors force both caps to shrink.
The witnesses may coincide. Cross-direction neighbor collisions instead
give a larger individual directional saving.
-/

namespace SmpMax.General

open FiniteProbability PermutationCounting LongerLogCertificate JointLogCertificate

namespace LongGap

theorem cut_side_ge_two {d N : ℕ} (owner : Fin d → Fin N) (t : Fin d)
    (hl : 24 ≤ t.val) (hr : t.val + 24 < d) (right : Bool) (π : Equiv.Perm (Fin N))
    (h1 : π (owner t) < π (localLabels owner t hl hr right 1))
    (h2 : π (owner t) < π (localLabels owner t hl hr right 2)) :
    2 ≤ if right then Gap.rightSize (Gap.revealedBy owner π t) t
      else Gap.leftSize (Gap.revealedBy owner π t) t := by
  have hclear (a : Fin 49) (ha : a.val = 1 ∨ a.val = 2) :
      localIndex t hl hr right a ∉ Gap.revealedBy owner π t := by
    intro hs
    have hy := (Finset.mem_filter.mp hs).2
    rcases ha with ha | ha
    · have he : a = 1 := Fin.ext ha
      subst a
      exact (not_lt_of_ge h1.le) hy
    · have he : a = 2 := Fin.ext ha
      subst a
      exact (not_lt_of_ge h2.le) hy
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply Gap.leftSize_ge_of_clear (by omega)
    intro i hi hit
    let a : Fin 49 := ⟨t.val - i.val, by omega⟩
    have ha : a.val = 1 ∨ a.val = 2 := by dsimp [a]; omega
    have he : localIndex t hl hr false a = i := by
      apply Fin.ext
      simp [localIndex, a, show t.val - i.val ≤ 24 by omega]
      omega
    simpa only [he] using hclear a ha
  · simp only [↓reduceIte]
    apply Gap.rightSize_ge_of_clear (by omega)
    intro i hit hi
    let a : Fin 49 := ⟨i.val - t.val, by omega⟩
    have ha : a.val = 1 ∨ a.val = 2 := by dsimp [a]; omega
    have he : localIndex t hl hr true a = i := by
      apply Fin.ext
      simp [localIndex, a, show i.val - t.val ≤ 24 by omega]
      omega
    simpa only [he] using hclear a ha

theorem joint_probability_ge {N : ℕ} (f : Fin 49 → Fin N) (hinj : Function.Injective f)
    (u v : Fin N) (hu0 : u ≠ f 0) (hv0 : v ≠ f 0)
    (hu : u ∉ afterLabels f 2 2) (hv : v ∉ afterLabels f 2 2) :
    (1 / 105 : ℝ) ≤ probability (beforeTwo u v (f 0) (afterLabels f 2 2)) := by
  classical
  have hc := afterLabels_card f hinj (by omega : 2 ≤ 23) (by omega : 2 ≤ 3)
  have hm := pivot_not_after f hinj 2 2
  by_cases he : u = v
  · subst v
    have hE : beforeTwo u u (f 0) (afterLabels f 2 2) =
        beforeOne u (f 0) (afterLabels f 2 2) := by
      ext π
      simp [beforeTwo, beforeOne]
    rw [hE, probability_beforeOne hu0 hu hm, hc]
    norm_num
  · rw [probability_beforeTwo he hu0 hv0 hu hv hm, hc]
    norm_num

end LongGap

namespace PartnerFrame

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

noncomputable def jointLoss (F : PartnerFrame I μ m) (π : Equiv.Perm (Fin (n + 48))) : ℝ :=
  JointGap.loss (Gap.leftSize (F.longSeen π) (LongPadded.position F.t))
    (Gap.rightSize (F.longSeen π) (LongPadded.position F.t))
    (F.cap false (LongPadded.earlier π m)) (F.cap true (LongPadded.earlier π m))

noncomputable def combinedMeanSaving (F : PartnerFrame I μ m) (hμ : Stable I μ) : ℝ :=
  F.longMeanSaving hμ false + F.longMeanSaving hμ true + average F.jointLoss

theorem jointLoss_nonneg (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (π : Equiv.Perm (Fin (n + 48))) : 0 ≤ F.jointLoss π := by
  apply JointGap.loss_nonneg (by positivity) (by positivity)
  · exact_mod_cast F.cap_le_long_gap hμ false π
  · exact_mod_cast F.cap_le_long_gap hμ true π

theorem combinedMeanSaving_ge (F : PartnerFrame I μ m) (hμ : Stable I μ) :
    F.longMeanSaving hμ false + F.longMeanSaving hμ true ≤ F.combinedMeanSaving hμ := by
  have h := average_mono (F.jointLoss_nonneg hμ)
  rw [average_const] at h
  unfold combinedMeanSaving
  linarith

theorem longDirectional_mirror (F : PartnerFrame I μ m) (hμ : Stable I μ) :
    (F.longDirectional hμ false).label 1 = (F.longDirectional hμ true).label 25 ∧
    (F.longDirectional hμ false).label 2 = (F.longDirectional hμ true).label 26 ∧
    (F.longDirectional hμ false).label 25 = (F.longDirectional hμ true).label 1 ∧
    (F.longDirectional hμ false).label 26 = (F.longDirectional hμ true).label 2 := by
  simp [longDirectional, LongGap.directionalData, LongGap.localLabels, LongGap.localIndex]

theorem jointMeanSaving_ge (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (u v : Fin (n + 48))
    (hu0 : u ≠ (F.longDirectional hμ true).label 0)
    (hv0 : v ≠ (F.longDirectional hμ true).label 0)
    (hu : u ∉ LongGap.afterLabels (F.longDirectional hμ true).label 2 2)
    (hv : v ∉ LongGap.afterLabels (F.longDirectional hμ true).label 2 2)
    (hcapL : ∀ π, π u < π (LongPadded.realLabel m) →
      F.cap false (LongPadded.earlier π m) ≤ 1)
    (hcapR : ∀ π, π v < π (LongPadded.realLabel m) →
      F.cap true (LongPadded.earlier π m) ≤ 1) :
    jointSaving ≤ average F.jointLoss := by
  classical
  let D := F.longDirectional hμ true
  let E := beforeTwo u v (D.label 0) (LongGap.afterLabels D.label 2 2)
  have hpoint (π : Equiv.Perm (Fin (n + 48))) :
      (if π ∈ E then Real.log (16 / 15 : ℝ) else 0) ≤ F.jointLoss π := by
    split_ifs with hπ
    · have he := (Finset.mem_filter.mp hπ).2
      have hafter (i : Fin 49) (hi : i = 1 ∨ i = 2 ∨ i = 25 ∨ i = 26) :
          π (D.label 0) < π (D.label i) := by
        apply he.2.2
        rw [LongGap.afterLabels_22]
        rcases hi with rfl | rfl | rfl | rfl <;> simp
      have hmir := F.longDirectional_mirror hμ
      have hleft1 : π (LongPadded.realLabel m) < π ((F.longDirectional hμ false).label 1) := by
        rw [hmir.1]
        simpa [D] using hafter 25 (by simp)
      have hleft2 : π (LongPadded.realLabel m) < π ((F.longDirectional hμ false).label 2) := by
        rw [hmir.2.1]
        simpa [D] using hafter 26 (by simp)
      have hright1 : π (LongPadded.realLabel m) < π (D.label 1) := by
        simpa [D] using hafter 1 (by simp)
      have hright2 : π (LongPadded.realLabel m) < π (D.label 2) := by
        simpa [D] using hafter 2 (by simp)
      have hL := LongGap.cut_side_ge_two F.longOwner (LongPadded.position F.t)
        (LongPadded.position_left F.t) (LongPadded.position_right F.t) false π
        (by simpa [longDirectional, LongGap.directionalData] using hleft1)
        (by simpa [longDirectional, LongGap.directionalData] using hleft2)
      have hR := LongGap.cut_side_ge_two F.longOwner (LongPadded.position F.t)
        (LongPadded.position_left F.t) (LongPadded.position_right F.t) true π
        (by simpa [D, longDirectional, LongGap.directionalData] using hright1)
        (by simpa [D, longDirectional, LongGap.directionalData] using hright2)
      have hl := hcapL π (by simpa [D] using he.1)
      have hr := hcapR π (by simpa [D] using he.2.1)
      apply JointGap.loss_ge (by positivity) (by positivity)
      · exact_mod_cast hL
      · exact_mod_cast hR
      · exact_mod_cast hl
      · exact_mod_cast hr
    · exact F.jointLoss_nonneg hμ π
  have hh := average_mono hpoint
  rw [average_event] at hh
  have hp := LongGap.joint_probability_ge D.label D.injective u v hu0 hv0 hu hv
  have hlog : 0 ≤ Real.log (16 / 15 : ℝ) := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hp hlog
  have hn := jointSaving_le
  change probability E * Real.log (16 / 15 : ℝ) ≤ _ at hh
  change (1 / 105 : ℝ) * Real.log (16 / 15 : ℝ) ≤ probability E * _ at hmul
  linarith

theorem combinedMeanSaving_regular (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (u v : Fin (n + 48))
    (hu0 : u ≠ (F.longDirectional hμ false).label 0)
    (hu1 : u ≠ (F.longDirectional hμ false).label 1)
    (hu2 : u ≠ (F.longDirectional hμ false).label 2)
    (hv0 : v ≠ (F.longDirectional hμ true).label 0)
    (hv1 : v ≠ (F.longDirectional hμ true).label 1)
    (hv2 : v ≠ (F.longDirectional hμ true).label 2)
    (hcapL : ∀ π, π u < π ((F.longDirectional hμ false).label 0) →
      (F.longDirectional hμ false).cap π ≤ 1)
    (hcapR : ∀ π, π v < π ((F.longDirectional hμ true).label 0) →
      (F.longDirectional hμ true).cap π ≤ 1) :
    2 * saving + jointSaving ≤ F.combinedMeanSaving hμ := by
  classical
  have hl := (F.longDirectional hμ false).second_step_saving u hu0 hu1 hu2 hcapL
  have hr := (F.longDirectional hμ true).second_step_saving v hv0 hv1 hv2 hcapR
  change saving ≤ F.longMeanSaving hμ false at hl
  change saving ≤ F.longMeanSaving hμ true at hr
  have hbase := F.combinedMeanSaving_ge hμ
  by_cases hul : u = (F.longDirectional hμ false).label 25 ∨
      u = (F.longDirectional hμ false).label 26
  · have h := (F.longDirectional hμ false).second_step_collision_saving u hu0 hu1 hu2 hul hcapL
    change saving + jointSaving ≤ F.longMeanSaving hμ false at h
    linarith
  · by_cases hvr : v = (F.longDirectional hμ true).label 25 ∨
        v = (F.longDirectional hμ true).label 26
    · have h := (F.longDirectional hμ true).second_step_collision_saving v hv0 hv1 hv2 hvr hcapR
      change saving + jointSaving ≤ F.longMeanSaving hμ true at h
      linarith
    · have hmir := F.longDirectional_mirror hμ
      have hu : u ∉ LongGap.afterLabels (F.longDirectional hμ true).label 2 2 := by
        rw [LongGap.afterLabels_22]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [hmir.1] at hu1
        rw [hmir.2.1] at hu2
        rw [hmir.2.2.1, hmir.2.2.2] at hul
        tauto
      have hv : v ∉ LongGap.afterLabels (F.longDirectional hμ true).label 2 2 := by
        rw [LongGap.afterLabels_22]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hj := F.jointMeanSaving_ge hμ u v (by simpa using hu0) hv0 hu hv
        (by simpa [longDirectional, LongGap.directionalData] using hcapL)
        (by simpa [longDirectional, LongGap.directionalData] using hcapR)
      unfold combinedMeanSaving
      linarith

end PartnerFrame

end SmpMax.General

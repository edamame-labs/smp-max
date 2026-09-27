import SmpMax.General.JointGapGeometry
import SmpMax.General.JointCharging

/-!
# Matching-level charging with the joint directional bonus

The same exceptional vertices and charge fibers are retained. Stronger
noncycle estimates cover every vertex missing the joint event.
-/

namespace SmpMax.General

open FiniteProbability LongerLogCertificate JointLogCertificate

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

namespace PartnerFrame

theorem longMeanSaving_short_joint (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (hs : F.sideLength right ≤ 1) :
    3 * (saving + jointSaving) ≤ F.longMeanSaving hμ right := by
  apply JointLogCertificate.short_ge.trans
  apply LongGap.DirectionalData.short_saving
  intro π
  exact (F.cap_le_sideLength right (LongPadded.earlier π m)).trans hs

theorem longMeanSaving_first_joint (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (hs : 1 ≤ F.sideLength right)
    (hne : directionOwner I μ right (directionOwner I μ right m) ≠ m) :
    3 * (saving + jointSaving) ≤ F.longMeanSaving hμ right := by
  let g := directionOwner I μ right
  have e1 : (⟨1, by decide⟩ : Fin 49) = 1 := by decide
  have h1 : (F.longDirectional hμ right).label 1 = LongPadded.realLabel (g m) := by
    simpa only [g, F.directionOwner_eq_neighbor right hs, e1] using
      F.longDirectional_label_neighbor hμ right (by omega : 1 ≤ 3) hs
  have hactive : g (g m) ≠ g m := by
    simpa only [g, F.directionOwner_eq_neighbor right hs] using
      F.neighborOwner_active hμ right (by omega : 0 < 1) hs
  apply LongGap.DirectionalData.first_step_joint_saving _ (LongPadded.realLabel (g (g m)))
  · rw [F.longDirectional_label_zero]
    exact fun h => hne (LongPadded.realLabel_injective h)
  · rw [h1]
    exact fun h => hactive (LongPadded.realLabel_injective h)
  · intro π hπ
    change F.cap right (LongPadded.earlier π m) ≤ 0
    apply F.cap_le_of_propagated hμ right hs
    rw [← F.directionOwner_eq_neighbor right hs, LongPadded.mem_earlier]
    simpa only [F.longDirectional_label_zero] using hπ

theorem second_joint_witness (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (hs : 2 ≤ F.sideLength right)
    (hne0 : directionOwner I μ right (F.neighborOwner right 2 hs) ≠ m)
    (hne1 : directionOwner I μ right (F.neighborOwner right 2 hs) ≠ directionOwner I μ right m) :
    ∃ u : Fin (n + 48), u ≠ (F.longDirectional hμ right).label 0 ∧
      u ≠ (F.longDirectional hμ right).label 1 ∧
      u ≠ (F.longDirectional hμ right).label 2 ∧
      ∀ π, π u < π ((F.longDirectional hμ right).label 0) →
        (F.longDirectional hμ right).cap π ≤ 1 := by
  let g := directionOwner I μ right
  let b := F.neighborOwner right 2 hs
  have hs1 : 1 ≤ F.sideLength right := by omega
  have e1 : (⟨1, by decide⟩ : Fin 49) = 1 := by decide
  have e2 : (⟨2, by decide⟩ : Fin 49) = 2 := by decide
  have h1 : (F.longDirectional hμ right).label 1 = LongPadded.realLabel (g m) := by
    simpa only [g, F.directionOwner_eq_neighbor right hs1, e1] using
      F.longDirectional_label_neighbor hμ right (by omega : 1 ≤ 3) hs1
  have h2 : (F.longDirectional hμ right).label 2 = LongPadded.realLabel b := by
    simpa only [b, e2] using F.longDirectional_label_neighbor hμ right (by omega : 2 ≤ 3) hs
  have hactive : g b ≠ b := F.neighborOwner_active hμ right (by omega : 0 < 2) hs
  refine ⟨LongPadded.realLabel (g b), ?_, ?_, ?_, ?_⟩
  · rw [F.longDirectional_label_zero]
    exact fun h => hne0 (LongPadded.realLabel_injective h)
  · rw [h1]
    exact fun h => hne1 (LongPadded.realLabel_injective h)
  · rw [h2]
    exact fun h => hactive (LongPadded.realLabel_injective h)
  · intro π hπ
    change F.cap right (LongPadded.earlier π m) ≤ 1
    apply F.cap_le_of_propagated hμ right hs
    rw [LongPadded.mem_earlier]
    simpa only [F.longDirectional_label_zero] using hπ

end PartnerFrame

theorem sum_combined_savings (hμ : Stable I μ) (F : ∀ m, PartnerFrame I μ m) :
    (n : ℝ) * (2 * saving + jointSaving) ≤ ∑ m, (F m).combinedMeanSaving hμ := by
  classical
  let g := fun right => directionOwner I μ right
  let b := fun right m => if h : 2 ≤ (F m).sideLength right then
    (F m).neighborOwner right 2 h else m
  let D := fun right => Finset.univ.filter (SuccessorCharging.Exceptional (g right) (b right))
  have hD (right : Bool) (m : Fin n) (hm : m ∈ D right) :
      SuccessorCharging.Exceptional (g right) (b right) m := (Finset.mem_filter.mp hm).2
  have hδ := LongerLogCertificate.saving_nonneg
  have hε := jointSaving_nonneg
  have hne (right : Bool) (m : Fin n) (hm : m ∉ D right)
      (hc : g right (g right m) = m) (hs : 2 ≤ (F m).sideLength right) :
      g right ((F m).neighborOwner right 2 hs) ≠ m ∧
        g right ((F m).neighborOwner right 2 hs) ≠ g right m := by
    have hs1 : 1 ≤ (F m).sideLength right := by omega
    constructor
    all_goals
      intro he
      apply hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hc, ?_, ?_, ?_⟩
      · simpa only [b, dif_pos hs] using (F m).neighborOwner_ne_self right (by omega) hs
      · simpa only [b, dif_pos hs, g, (F m).directionOwner_eq_neighbor right hs1] using
          (F m).neighborOwner_distinct right hs hs1 (by omega)
      · first
          | exact Or.inl (by simpa only [b, dif_pos hs] using he)
          | exact Or.inr (by simpa only [b, dif_pos hs] using he)
  have hbase (right : Bool) (m : Fin n) (hm : m ∉ D right) :
      saving ≤ (F m).longMeanSaving hμ right := by
    by_cases hs : (F m).sideLength right ≤ 1
    · have h := (F m).longMeanSaving_short_joint hμ right hs
      linarith
    · have hs2 : 2 ≤ (F m).sideLength right := by omega
      by_cases hc : g right (g right m) = m
      · have hn := hne right m hm hc hs2
        exact (F m).longMeanSaving_second hμ right hs2 hn.1 hn.2
      · have h := (F m).longMeanSaving_first_joint hμ right (by omega) hc
        linarith
  have hbad (right : Bool) (m : Fin n) (hc : g right (g right m) ≠ m) :
      3 * (saving + jointSaving) ≤ (F m).longMeanSaving hμ right := by
    by_cases hs : (F m).sideLength right ≤ 1
    · exact (F m).longMeanSaving_short_joint hμ right hs
    · exact (F m).longMeanSaving_first_joint hμ right (by omega) hc
  have hboth (m : Fin n) (h₀ : m ∉ D false) (h₁ : m ∉ D true)
      (hc₀ : g false (g false m) = m) (hc₁ : g true (g true m) = m) :
      2 * saving + jointSaving ≤ (F m).combinedMeanSaving hμ := by
    have hsum := (F m).combinedMeanSaving_ge hμ
    by_cases hs₀ : (F m).sideLength false ≤ 1
    · have hleft := (F m).longMeanSaving_short_joint hμ false hs₀
      have hright := hbase true m h₁
      linarith
    · by_cases hs₁ : (F m).sideLength true ≤ 1
      · have hleft := hbase false m h₀
        have hright := (F m).longMeanSaving_short_joint hμ true hs₁
        linarith
      · have hs₀' : 2 ≤ (F m).sideLength false := by omega
        have hs₁' : 2 ≤ (F m).sideLength true := by omega
        have hn₀ := hne false m h₀ hc₀ hs₀'
        have hn₁ := hne true m h₁ hc₁ hs₁'
        obtain ⟨u, hu0, hu1, hu2, hcapu⟩ :=
          (F m).second_joint_witness hμ false hs₀' hn₀.1 hn₀.2
        obtain ⟨v, hv0, hv1, hv2, hcapv⟩ :=
          (F m).second_joint_witness hμ true hs₁' hn₁.1 hn₁.2
        exact (F m).combinedMeanSaving_regular hμ u v hu0 hu1 hu2 hv0 hv1 hv2 hcapu hcapv
  have h := SuccessorCharging.sum_joint_saving_ge (g false) (g true) (b false) (b true)
    (D false) (D true) (hD false) (hD true)
    (fun m => (F m).longMeanSaving hμ false) (fun m => (F m).longMeanSaving hμ true)
    (fun m => (F m).combinedMeanSaving hμ) saving jointSaving hδ hε
    (fun m => (F m).longMeanSaving_nonneg hμ false)
    (fun m => (F m).longMeanSaving_nonneg hμ true)
    (hbase false) (hbase true) (hbad false) (hbad true)
    (fun m => (F m).combinedMeanSaving_ge hμ) hboth
  simpa only [Fintype.card_fin] using h

end SmpMax.General

import SmpMax.General.PaddedSupport
import SmpMax.General.SuccessorCharging

/-! # Matching-level local classes and the two-to-one charging argument -/

namespace SmpMax.General

open FiniteProbability

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

namespace PartnerFrame

noncomputable def meanSaving (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool) : ℝ :=
  average (F.directional hμ right).loss

theorem meanSaving_nonneg (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool) :
    0 ≤ F.meanSaving hμ right := by
  have h := average_mono ((F.directional hμ right).loss_nonneg)
  rw [average_const] at h
  exact h

theorem meanSaving_short (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (hs : F.sideLength right ≤ 1) :
    3 * BidirectionalLogCertificate.saving ≤ F.meanSaving hμ right := by
  apply BidirectionalLogCertificate.shortSideSaving_ge_three.trans
  apply LocalGap.DirectionalData.short_saving
  intro π
  exact (F.cap_le_sideLength right (Padded.earlier π m)).trans hs

theorem meanSaving_first (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (hs : 1 ≤ F.sideLength right)
    (hne : directionOwner I μ right (directionOwner I μ right m) ≠ m) :
    3 * BidirectionalLogCertificate.saving ≤ F.meanSaving hμ right := by
  let g := directionOwner I μ right
  have e1 : (⟨1, by decide⟩ : Fin 7) = 1 := by decide
  have h1 : (F.directional hμ right).label 1 = Padded.realLabel (g m) := by
    simpa only [g, F.directionOwner_eq_neighbor right hs, e1] using
      F.directional_label_neighbor hμ right (by omega : 1 ≤ 3) hs
  have hactive : g (g m) ≠ g m := by
    simpa only [g, F.directionOwner_eq_neighbor right hs] using
      F.neighborOwner_active hμ right (by omega : 0 < 1) hs
  apply BidirectionalLogCertificate.firstStepSaving_ge_three.trans
  apply LocalGap.DirectionalData.first_step_saving _ (Padded.realLabel (g (g m)))
  · rw [F.directional_label_zero]
    exact fun h => hne (Padded.realLabel_injective h)
  · rw [h1]
    exact fun h => hactive (Padded.realLabel_injective h)
  · intro π hπ
    change F.cap right (Padded.earlier π m) ≤ 0
    apply F.cap_le_of_propagated hμ right hs
    rw [← F.directionOwner_eq_neighbor right hs, Padded.mem_earlier]
    simpa only [F.directional_label_zero] using hπ

theorem meanSaving_second (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (hs : 2 ≤ F.sideLength right)
    (hne0 : directionOwner I μ right (F.neighborOwner right 2 hs) ≠ m)
    (hne1 : directionOwner I μ right (F.neighborOwner right 2 hs) ≠ directionOwner I μ right m) :
    BidirectionalLogCertificate.saving ≤ F.meanSaving hμ right := by
  let g := directionOwner I μ right
  let b := F.neighborOwner right 2 hs
  have hs1 : 1 ≤ F.sideLength right := by omega
  have e1 : (⟨1, by decide⟩ : Fin 7) = 1 := by decide
  have e2 : (⟨2, by decide⟩ : Fin 7) = 2 := by decide
  have h1 : (F.directional hμ right).label 1 = Padded.realLabel (g m) := by
    simpa only [g, F.directionOwner_eq_neighbor right hs1, e1] using
      F.directional_label_neighbor hμ right (by omega : 1 ≤ 3) hs1
  have h2 : (F.directional hμ right).label 2 = Padded.realLabel b := by
    simpa only [b, e2] using F.directional_label_neighbor hμ right (by omega : 2 ≤ 3) hs
  have hactive : g b ≠ b := F.neighborOwner_active hμ right (by omega : 0 < 2) hs
  apply LocalGap.DirectionalData.second_step_saving _ (Padded.realLabel (g b))
  · rw [F.directional_label_zero]
    exact fun h => hne0 (Padded.realLabel_injective h)
  · rw [h1]
    exact fun h => hne1 (Padded.realLabel_injective h)
  · rw [h2]
    exact fun h => hactive (Padded.realLabel_injective h)
  · intro π hπ
    change F.cap right (Padded.earlier π m) ≤ 1
    apply F.cap_le_of_propagated hμ right hs
    rw [Padded.mem_earlier]
    simpa only [F.directional_label_zero] using hπ

end PartnerFrame

/-- Each direction saves at least one unit per real man, after charging exceptions. -/
theorem sum_directional_savings (hμ : Stable I μ) (F : ∀ m, PartnerFrame I μ m) (right : Bool) :
    (n : ℝ) * BidirectionalLogCertificate.saving ≤ ∑ m, (F m).meanSaving hμ right := by
  classical
  let g := directionOwner I μ right
  let b := fun m => if h : 2 ≤ (F m).sideLength right then (F m).neighborOwner right 2 h else m
  let D := Finset.univ.filter (SuccessorCharging.Exceptional g b)
  have hδ := BidirectionalLogCertificate.saving_nonneg
  have hc := SuccessorCharging.sum_saving_ge g b D
    (fun m hm => (Finset.mem_filter.mp hm).2) _ _ hδ
    (fun m => (F m).meanSaving_nonneg hμ right)
  simp only [Fintype.card_fin] at hc
  apply hc
  · intro m hm
    by_cases hs : (F m).sideLength right ≤ 1
    · have h := (F m).meanSaving_short hμ right hs
      linarith
    · have hs2 : 2 ≤ (F m).sideLength right := by omega
      have hs1 : 1 ≤ (F m).sideLength right := by omega
      by_cases hcycle : g (g m) = m
      · apply (F m).meanSaving_second hμ right hs2
        all_goals
          intro he
          apply hm
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, hcycle, ?_, ?_, ?_⟩
          · simpa only [b, dif_pos hs2] using (F m).neighborOwner_ne_self right (by omega) hs2
          · simpa only [b, dif_pos hs2, g, (F m).directionOwner_eq_neighbor right hs1] using
              (F m).neighborOwner_distinct right hs2 hs1 (by omega)
          · first
              | exact Or.inl (by simpa only [b, dif_pos hs2] using he)
              | exact Or.inr (by simpa only [b, dif_pos hs2] using he)
      · have h := (F m).meanSaving_first hμ right hs1 hcycle
        linarith
  · intro m hcycle
    by_cases hs : (F m).sideLength right ≤ 1
    · exact (F m).meanSaving_short hμ right hs
    · exact (F m).meanSaving_first hμ right (by omega) hcycle

end SmpMax.General

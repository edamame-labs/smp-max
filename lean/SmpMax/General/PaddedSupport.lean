import SmpMax.General.PartnerFrame
import SmpMax.General.PaddedOwners
import SmpMax.General.LocalGapGeometry

/-! # The common padded gap bounds the exact conditional partner support -/

namespace SmpMax.General.PartnerFrame

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

def paddedOwner (F : PartnerFrame I μ m) : Fin (F.L.length + 6) → Fin (n + 6) :=
  Padded.owner (fun j => μ.symm (F.L.partner j))

theorem paddedOwner_injective (F : PartnerFrame I μ m) : Function.Injective F.paddedOwner :=
  Padded.owner_injective _ (F.L.owners_injective μ)

@[simp] theorem paddedOwner_pivot (F : PartnerFrame I μ m) :
    F.paddedOwner (Padded.position F.t) = Padded.realLabel m := by
  simp [paddedOwner, F.reference]

def paddedSeen (F : PartnerFrame I μ m) (π : Equiv.Perm (Fin (n + 6))) :
    Finset (Fin (F.L.length + 6)) := Gap.revealedBy F.paddedOwner π (Padded.position F.t)

@[simp] theorem real_position_seen (F : PartnerFrame I μ m)
    (π : Equiv.Perm (Fin (n + 6))) (i : Fin F.L.length) :
    Padded.position i ∈ F.paddedSeen π ↔ μ.symm (F.L.partner i) ∈ Padded.earlier π m := by
  simp [paddedSeen, Gap.revealedBy, paddedOwner, F.reference]

theorem support_between_padded (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (π : Equiv.Perm (Fin (n + 6))) {j : Fin F.L.length}
    (hj : j ∈ F.L.indexSupport μ (Padded.earlier π m)) :
    Gap.lower (F.paddedSeen π) (Padded.position F.t) ≤ j.val + 3 ∧
      j.val + 4 < Gap.upper (F.paddedSeen π) (Padded.position F.t) := by
  classical
  obtain ⟨ν, hν, hνj⟩ := (Finset.mem_filter.mp hj).2
  constructor
  · rcases Gap.lower_spec (F.paddedSeen π) (Padded.position F.t) with h | ⟨i, hi, hit, h⟩
    · omega
    · have hv : i.val < F.t.val + 3 := hit
      by_cases hi3 : i.val < 3
      · omega
      · let a : Fin F.L.length := ⟨i.val - 3, by have := F.t.isLt; omega⟩
        have he : Padded.position a = i := by apply Fin.ext; dsimp [Padded.position, a]; omega
        have hseen : μ.symm (F.L.partner a) ∈ Padded.earlier π m := by
          rw [← F.real_position_seen π a, he]
          exact hi
        have hat : a < F.t := by change i.val - 3 < F.t.val; omega
        have hp : I.men m (F.L.partner a) < I.men m (μ m) := by
          rw [← F.reference]
          exact F.L.increasing hat
        have hb := compatible_lower_barrier (F.L.stable a) hμ hν hseen hp
        rw [hνj] at hb
        have haj := F.L.increasing.lt_iff_lt.mp hb
        change i.val - 3 < j.val at haj
        omega
  · rcases Gap.upper_spec (F.paddedSeen π) (Padded.position F.t) with h | ⟨i, hi, hti, h⟩
    · have := j.isLt
      omega
    · have hv : F.t.val + 3 < i.val := hti
      by_cases hiend : F.L.length + 3 ≤ i.val
      · have := j.isLt
        omega
      · let a : Fin F.L.length := ⟨i.val - 3, by omega⟩
        have he : Padded.position a = i := by apply Fin.ext; dsimp [Padded.position, a]; omega
        have hseen : μ.symm (F.L.partner a) ∈ Padded.earlier π m := by
          rw [← F.real_position_seen π a, he]
          exact hi
        have hta : F.t < a := by change F.t.val < i.val - 3; omega
        have hp : I.men m (μ m) < I.men m (F.L.partner a) := by
          rw [← F.reference]
          exact F.L.increasing hta
        have hb := compatible_upper_barrier (F.L.stable a) hμ hν hseen hp
        rw [hνj] at hb
        have hja := F.L.increasing.lt_iff_lt.mp hb
        change j.val < i.val - 3 at hja
        omega

theorem cap_le_padded (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (π : Equiv.Perm (Fin (n + 6))) :
    F.cap right (Padded.earlier π m) ≤
      if right then Gap.rightSize (F.paddedSeen π) (Padded.position F.t)
      else Gap.leftSize (F.paddedSeen π) (Padded.position F.t) := by
  have hl := Gap.lower_le_pivot (F.paddedSeen π) (Padded.position F.t)
  have hr := Gap.pivot_lt_upper (F.paddedSeen π) (Padded.position F.t)
  cases right <;> simp only [cap, Bool.false_eq_true, ↓reduceIte,
    SupportCaps.left, SupportCaps.right] <;> apply Finset.sup_le <;> intro j hj
  all_goals
    have hb := F.support_between_padded hμ π hj
    simp only [Gap.leftSize, Gap.rightSize, Padded.position] at *
    omega

noncomputable def directional (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool) :
    LocalGap.DirectionalData (n + 6) :=
  LocalGap.directionalData F.paddedOwner F.paddedOwner_injective (Padded.position F.t)
    (Padded.position_left F.t) (Padded.position_right F.t) right
    (fun π => F.cap right (Padded.earlier π m)) (F.cap_le_padded hμ right)

@[simp] theorem directional_label_zero (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (right : Bool) : (F.directional hμ right).label 0 = Padded.realLabel m := by
  simp [directional, LocalGap.directionalData]

theorem directional_label_neighbor (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (right : Bool) {k : ℕ} (hk3 : k ≤ 3) (hk : k ≤ F.sideLength right) :
    (F.directional hμ right).label ⟨k, by omega⟩ =
      Padded.realLabel (F.neighborOwner right k hk) := by
  change F.paddedOwner (LocalGap.localIndex (Padded.position F.t) _ _ right ⟨k, by omega⟩) = _
  have he : LocalGap.localIndex (Padded.position F.t) (Padded.position_left F.t)
      (Padded.position_right F.t) right ⟨k, by omega⟩ = Padded.position (F.neighbor right k hk) := by
    apply Fin.ext
    cases right <;> simp [LocalGap.localIndex, Padded.position, neighbor, hk3] <;>
      simp only [sideLength, Bool.false_eq_true, ↓reduceIte] at hk <;> omega
  rw [he]
  exact Padded.owner_position _ _

end SmpMax.General.PartnerFrame

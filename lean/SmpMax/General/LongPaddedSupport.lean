import SmpMax.General.PartnerFrame
import SmpMax.General.LongPaddedOwners
import SmpMax.General.LongGapGeometry

/-! # The common padded gap bounds the exact conditional partner support -/

namespace SmpMax.General.PartnerFrame

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

def longOwner (F : PartnerFrame I μ m) : Fin (F.L.length + 48) → Fin (n + 48) :=
  LongPadded.owner (fun j => μ.symm (F.L.partner j))

theorem longOwner_injective (F : PartnerFrame I μ m) : Function.Injective F.longOwner :=
  LongPadded.owner_injective _ (F.L.owners_injective μ)

@[simp] theorem longOwner_pivot (F : PartnerFrame I μ m) :
    F.longOwner (LongPadded.position F.t) = LongPadded.realLabel m := by
  simp [longOwner, F.reference]

def longSeen (F : PartnerFrame I μ m) (π : Equiv.Perm (Fin (n + 48))) :
    Finset (Fin (F.L.length + 48)) := Gap.revealedBy F.longOwner π (LongPadded.position F.t)

@[simp] theorem long_real_position_seen (F : PartnerFrame I μ m)
    (π : Equiv.Perm (Fin (n + 48))) (i : Fin F.L.length) :
    LongPadded.position i ∈ F.longSeen π ↔ μ.symm (F.L.partner i) ∈ LongPadded.earlier π m := by
  simp [longSeen, Gap.revealedBy, longOwner, F.reference]

theorem support_between_long_gap (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (π : Equiv.Perm (Fin (n + 48))) {j : Fin F.L.length}
    (hj : j ∈ F.L.indexSupport μ (LongPadded.earlier π m)) :
    Gap.lower (F.longSeen π) (LongPadded.position F.t) ≤ j.val + 24 ∧
      j.val + 25 < Gap.upper (F.longSeen π) (LongPadded.position F.t) := by
  classical
  obtain ⟨ν, hν, hνj⟩ := (Finset.mem_filter.mp hj).2
  constructor
  · rcases Gap.lower_spec (F.longSeen π) (LongPadded.position F.t) with h | ⟨i, hi, hit, h⟩
    · omega
    · have hv : i.val < F.t.val + 24 := hit
      by_cases hi3 : i.val < 24
      · omega
      · let a : Fin F.L.length := ⟨i.val - 24, by have := F.t.isLt; omega⟩
        have he : LongPadded.position a = i := by
          apply Fin.ext; dsimp [LongPadded.position, a]; omega
        have hseen : μ.symm (F.L.partner a) ∈ LongPadded.earlier π m := by
          rw [← F.long_real_position_seen π a, he]
          exact hi
        have hat : a < F.t := by change i.val - 24 < F.t.val; omega
        have hp : I.men m (F.L.partner a) < I.men m (μ m) := by
          rw [← F.reference]
          exact F.L.increasing hat
        have hb := compatible_lower_barrier (F.L.stable a) hμ hν hseen hp
        rw [hνj] at hb
        have haj := F.L.increasing.lt_iff_lt.mp hb
        change i.val - 24 < j.val at haj
        omega
  · rcases Gap.upper_spec (F.longSeen π) (LongPadded.position F.t) with h | ⟨i, hi, hti, h⟩
    · have := j.isLt
      omega
    · have hv : F.t.val + 24 < i.val := hti
      by_cases hiend : F.L.length + 24 ≤ i.val
      · have := j.isLt
        omega
      · let a : Fin F.L.length := ⟨i.val - 24, by omega⟩
        have he : LongPadded.position a = i := by
          apply Fin.ext; dsimp [LongPadded.position, a]; omega
        have hseen : μ.symm (F.L.partner a) ∈ LongPadded.earlier π m := by
          rw [← F.long_real_position_seen π a, he]
          exact hi
        have hta : F.t < a := by change F.t.val < i.val - 24; omega
        have hp : I.men m (μ m) < I.men m (F.L.partner a) := by
          rw [← F.reference]
          exact F.L.increasing hta
        have hb := compatible_upper_barrier (F.L.stable a) hμ hν hseen hp
        rw [hνj] at hb
        have hja := F.L.increasing.lt_iff_lt.mp hb
        change j.val < i.val - 24 at hja
        omega

theorem cap_le_long_gap (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    (π : Equiv.Perm (Fin (n + 48))) :
    F.cap right (LongPadded.earlier π m) ≤
      if right then Gap.rightSize (F.longSeen π) (LongPadded.position F.t)
      else Gap.leftSize (F.longSeen π) (LongPadded.position F.t) := by
  have hl := Gap.lower_le_pivot (F.longSeen π) (LongPadded.position F.t)
  have hr := Gap.pivot_lt_upper (F.longSeen π) (LongPadded.position F.t)
  cases right <;> simp only [cap, Bool.false_eq_true, ↓reduceIte,
    SupportCaps.left, SupportCaps.right] <;> apply Finset.sup_le <;> intro j hj
  all_goals
    have hb := F.support_between_long_gap hμ π hj
    simp only [Gap.leftSize, Gap.rightSize, LongPadded.position] at *
    omega

noncomputable def longDirectional (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool) :
    LongGap.DirectionalData (n + 48) :=
  LongGap.directionalData F.longOwner F.longOwner_injective (LongPadded.position F.t)
    (LongPadded.position_left F.t) (LongPadded.position_right F.t) right
    (fun π => F.cap right (LongPadded.earlier π m)) (F.cap_le_long_gap hμ right)

@[simp] theorem longDirectional_label_zero (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (right : Bool) : (F.longDirectional hμ right).label 0 = LongPadded.realLabel m := by
  simp [longDirectional, LongGap.directionalData]

theorem longDirectional_label_neighbor (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (right : Bool) {k : ℕ} (hk3 : k ≤ 3) (hk : k ≤ F.sideLength right) :
    (F.longDirectional hμ right).label ⟨k, by omega⟩ =
      LongPadded.realLabel (F.neighborOwner right k hk) := by
  change F.longOwner (LongGap.localIndex (LongPadded.position F.t) _ _ right ⟨k, by omega⟩) = _
  have he : LongGap.localIndex (LongPadded.position F.t) (LongPadded.position_left F.t)
      (LongPadded.position_right F.t) right ⟨k, by omega⟩ =
        LongPadded.position (F.neighbor right k hk) := by
    apply Fin.ext
    have hk24 : k ≤ 24 := by omega
    cases right <;> simp [LongGap.localIndex, LongPadded.position, neighbor, hk24] <;>
      simp only [sideLength, Bool.false_eq_true, ↓reduceIte] at hk <;> omega
  rw [he]
  exact LongPadded.owner_position _ _

end SmpMax.General.PartnerFrame

import SmpMax.General.BidirectionalPropagation
import SmpMax.General.SupportCaps

/-! # Partner lists centered at a fixed stable outcome -/

namespace SmpMax.General

variable {n : ℕ} {I : Profile n} {μ : Matching n} {m : Fin n}

structure PartnerFrame (I : Profile n) (μ : Matching n) (m : Fin n) where
  L : PartnerOrder I m
  t : Fin L.length
  reference : L.partner t = μ m

noncomputable def partnerFrame (hμ : Stable I μ) (m : Fin n) : PartnerFrame I μ m := by
  let L := orderedPartners I m
  exact ⟨L, Classical.choose (L.complete (μ m) (hμ.stablePair m)),
    Classical.choose_spec (L.complete (μ m) (hμ.stablePair m))⟩

noncomputable def directionOwner (I : Profile n) (μ : Matching n)
    (right : Bool) (m : Fin n) : Fin n :=
  if right then successorOwner I μ m else predecessorOwner I μ m

namespace PartnerFrame

def sideLength (F : PartnerFrame I μ m) (right : Bool) : ℕ :=
  if right then F.L.length - F.t.val - 1 else F.t.val

def neighbor (F : PartnerFrame I μ m) (right : Bool) (k : ℕ)
    (hk : k ≤ F.sideLength right) : Fin F.L.length :=
  if h : right then ⟨F.t.val + k, by have := F.t.isLt; simp [sideLength, h] at hk; omega⟩
  else ⟨F.t.val - k, by have := F.t.isLt; omega⟩

noncomputable def neighborOwner (F : PartnerFrame I μ m) (right : Bool) (k : ℕ)
    (hk : k ≤ F.sideLength right) : Fin n := μ.symm (F.L.partner (F.neighbor right k hk))

@[simp] theorem neighbor_zero (F : PartnerFrame I μ m) (right : Bool) :
    F.neighbor right 0 (Nat.zero_le _) = F.t := by cases right <;> simp [neighbor]

theorem neighborOwner_ne_self (F : PartnerFrame I μ m) (right : Bool) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ F.sideLength right) : F.neighborOwner right k hk ≠ m := by
  apply F.L.owner_ne_target μ F.reference
  intro he
  have hv := congrArg Fin.val he
  cases right <;> simp [neighbor, sideLength] at hv hk <;> omega

theorem neighborOwner_distinct (F : PartnerFrame I μ m) (right : Bool) {k l : ℕ}
    (hk : k ≤ F.sideLength right) (hl : l ≤ F.sideLength right) (hne : k ≠ l) :
    F.neighborOwner right k hk ≠ F.neighborOwner right l hl := by
  intro he
  have hi := F.L.owners_injective μ he
  have hv := congrArg Fin.val hi
  cases right <;> simp [neighbor, sideLength] at hv hk hl <;> omega

/-- The first list position in either direction is the previously defined propagation map. -/
theorem directionOwner_eq_neighbor (F : PartnerFrame I μ m) (right : Bool)
    (hk : 1 ≤ F.sideLength right) :
    directionOwner I μ right m = F.neighborOwner right 1 hk := by
  classical
  cases right
  · let i := F.neighbor false 1 hk
    have hit : i < F.t := by
      simp only [sideLength, Bool.false_eq_true, ↓reduceIte] at hk
      change F.t.val - 1 < F.t.val
      omega
    have hm : F.L.partner i ∈ betterPartners I μ m := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.L.stable i, ?_⟩
      rw [← F.reference]
      exact F.L.increasing hit
    have hs := nextBetterPartner_spec ⟨_, hm⟩
    obtain ⟨j, hj⟩ := F.L.complete _ hs.1
    have hjt : j < F.t := F.L.increasing.lt_iff_lt.mp (by rw [hj, F.reference]; exact hs.2.1)
    have hji : j ≤ i := by change j.val ≤ F.t.val - 1; exact Nat.le_sub_one_of_lt hjt
    have hle := F.L.increasing.monotone hji
    rw [hj] at hle
    have he := (I.men m).injective (le_antisymm hle (hs.2.2 _ hm))
    simpa only [directionOwner, Bool.false_eq_true, ↓reduceIte, predecessorOwner, neighborOwner]
      using congrArg μ.symm he
  · let i := F.neighbor true 1 hk
    have hti : F.t < i := by change F.t.val < F.t.val + 1; omega
    have hm : F.L.partner i ∈ worsePartners I μ m := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.L.stable i, ?_⟩
      rw [← F.reference]
      exact F.L.increasing hti
    have hs := nextWorsePartner_spec ⟨_, hm⟩
    obtain ⟨j, hj⟩ := F.L.complete _ hs.1
    have htj : F.t < j := F.L.increasing.lt_iff_lt.mp (by rw [hj, F.reference]; exact hs.2.1)
    have hij : i ≤ j := by change F.t.val + 1 ≤ j.val; exact htj
    have hle := F.L.increasing.monotone hij
    rw [hj] at hle
    have he := (I.men m).injective (le_antisymm (hs.2.2 _ hm) hle)
    simpa only [directionOwner, ↓reduceIte, successorOwner, neighborOwner]
      using congrArg μ.symm he

theorem neighborOwner_active (F : PartnerFrame I μ m) (hμ : Stable I μ) (right : Bool)
    {k : ℕ} (hk0 : 0 < k) (hk : k ≤ F.sideLength right) :
    directionOwner I μ right (F.neighborOwner right k hk) ≠ F.neighborOwner right k hk := by
  classical
  let w := F.L.partner (F.neighbor right k hk)
  obtain ⟨ν, hν, hνm⟩ := F.L.stable (F.neighbor right k hk)
  cases right
  · have hbefore : I.men m w < I.men m (μ m) := by
      rw [← F.reference]
      apply F.L.increasing
      simp only [sideLength, Bool.false_eq_true, ↓reduceIte] at hk
      change F.t.val - k < F.t.val
      omega
    have hc := crossing_forces_owner_better (F.L.stable _) hμ hν hbefore
      (by rw [hνm])
    exact predecessorOwner_ne_of_better ⟨ν (μ.symm w),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hν.stablePair _, hc⟩⟩
  · have hbefore : I.men m (μ m) < I.men m w := by
      rw [← F.reference]
      apply F.L.increasing
      change F.t.val < F.t.val + k
      omega
    have hc := crossing_forces_owner_worse (F.L.stable _) hμ hν hbefore
      (by rw [hνm])
    exact successorOwner_ne_of_worse ⟨ν (μ.symm w),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hν.stablePair _, hc⟩⟩

noncomputable def cap (F : PartnerFrame I μ m) (right : Bool) (R : Finset (Fin n)) : ℕ :=
  if right then SupportCaps.right (F.L.indexSupport μ R) F.t
  else SupportCaps.left (F.L.indexSupport μ R) F.t

theorem cap_le_sideLength (F : PartnerFrame I μ m) (right : Bool) (R : Finset (Fin n)) :
    F.cap right R ≤ F.sideLength right := by
  cases right
  · simpa only [cap, sideLength, Bool.false_eq_true, ↓reduceIte] using
      SupportCaps.left_le_pivot (F.L.indexSupport μ R) F.t
  · have h := SupportCaps.right_lt_end (F.L.indexSupport μ R) F.t
    simp only [cap, sideLength, ↓reduceIte]
    omega

/-- Revealing the propagated owner cuts the support before the chosen list position. -/
theorem cap_le_of_propagated (F : PartnerFrame I μ m) (hμ : Stable I μ)
    (right : Bool) {q : ℕ} (hk : q + 1 ≤ F.sideLength right) (R : Finset (Fin n))
    (hseen : directionOwner I μ right (F.neighborOwner right (q + 1) hk) ∈ R) :
    F.cap right R ≤ q := by
  classical
  simp only [cap]
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply SupportCaps.left_le
    intro j hj
    obtain ⟨ν, hν, hνj⟩ := (Finset.mem_filter.mp hj).2
    have hbefore : I.men m (F.L.partner (F.neighbor false (q + 1) hk)) < I.men m (μ m) := by
      rw [← F.reference]
      apply F.L.increasing
      simp only [sideLength, Bool.false_eq_true, ↓reduceIte] at hk
      change F.t.val - (q + 1) < F.t.val
      omega
    have hc := compatible_predecessor_lower_barrier (F.L.stable _) hμ hν hbefore hseen
    rw [hνj] at hc
    have hi := F.L.increasing.lt_iff_lt.mp hc
    change F.t.val - (q + 1) < j.val at hi
    simp only [sideLength, Bool.false_eq_true, ↓reduceIte] at hk
    omega
  · simp only [↓reduceIte]
    apply SupportCaps.right_le
    intro j hj
    obtain ⟨ν, hν, hνj⟩ := (Finset.mem_filter.mp hj).2
    have hbefore : I.men m (μ m) < I.men m (F.L.partner (F.neighbor true (q + 1) hk)) := by
      rw [← F.reference]
      apply F.L.increasing
      change F.t.val < F.t.val + (q + 1)
      omega
    have hc := compatible_successor_upper_barrier (F.L.stable _) hμ hν hbefore hseen
    rw [hνj] at hc
    have hi := F.L.increasing.lt_iff_lt.mp hc
    change j.val < F.t.val + (q + 1) at hi
    omega

end PartnerFrame
end SmpMax.General

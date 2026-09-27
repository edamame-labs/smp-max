import SmpMax.General.Barriers
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

/-!
# Conditional support lies in a stable-partner interval

The ordered list contains all and only stable partners, in strict
preference order. We construct such a list for every profile and man.
Positions are shifted by one, so the two sentinels are `0` and `d + 1`.
Thus the draft's gap `b - a - 1` has the same value here without needing
a negative sentinel.
-/

namespace SmpMax.General

variable {n : ℕ}

/-- A complete sorted list of stable partners, with no repetitions. -/
structure PartnerOrder (I : Profile n) (m : Fin n) where
  length : ℕ
  partner : Fin length → Fin n
  increasing : StrictMono (fun j => I.men m (partner j))
  stable : ∀ j, StablePair I m (partner j)
  complete : ∀ w, StablePair I m w → ∃ j, partner j = w

/-- Sorting the set of stable ranks constructs the required list unconditionally. -/
noncomputable def orderedPartners (I : Profile n) (m : Fin n) : PartnerOrder I m := by
  classical
  let ranks := Finset.univ.filter (fun r => StablePair I m ((I.men m).symm r))
  refine {
    length := ranks.card
    partner := fun j => (I.men m).symm (ranks.orderEmbOfFin rfl j)
    increasing := ?_
    stable := ?_
    complete := ?_
  }
  · simpa only [Equiv.apply_symm_apply] using (ranks.orderEmbOfFin rfl).strictMono
  · intro j
    exact (Finset.mem_filter.mp (ranks.orderEmbOfFin_mem rfl j)).2
  · intro w hw
    have hr : I.men m w ∈ ranks := by simpa [ranks] using hw
    have he : I.men m w ∈ Set.range (ranks.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hr
    obtain ⟨j, hj⟩ := he
    exact ⟨j, by simp only [hj, Equiv.symm_apply_apply]⟩

variable {I : Profile n} {m : Fin n}

theorem PartnerOrder.injective (L : PartnerOrder I m) : Function.Injective L.partner := by
  intro i j hij
  exact L.increasing.injective (congrArg (I.men m) hij)

/-- For a fixed outcome, different stable partners have different male owners. -/
theorem PartnerOrder.owners_injective (L : PartnerOrder I m) (μ : Matching n) :
    Function.Injective (fun j => μ.symm (L.partner j)) :=
  μ.symm.injective.comp L.injective

/-- Every other stable partner is owned by a man different from the target man. -/
theorem PartnerOrder.owner_ne_target (L : PartnerOrder I m) (μ : Matching n)
    {t j : Fin L.length} (ht : L.partner t = μ m) (hne : j ≠ t) :
    μ.symm (L.partner j) ≠ m := by
  intro heq
  apply hne
  apply L.injective
  rw [ht]
  simpa only [Equiv.apply_symm_apply] using congrArg μ heq

/-- Support indexed in the compressed list of stable partners, not all rank positions. -/
noncomputable def PartnerOrder.indexSupport (L : PartnerOrder I m) (μ : Matching n)
    (revealed : Finset (Fin n)) : Finset (Fin L.length) := by
  classical
  exact Finset.univ.filter (fun j => L.partner j ∈ PartnerSupport I μ revealed m)

/-- A real lower barrier or the left sentinel. -/
def PartnerOrder.LowerCut (L : PartnerOrder I m) (μ : Matching n)
    (revealed : Finset (Fin n)) (t : Fin L.length) (a : ℕ) : Prop :=
  a = 0 ∨ ∃ i : Fin L.length,
    i < t ∧ μ.symm (L.partner i) ∈ revealed ∧ a = i.val + 1

/-- A real upper barrier or the right sentinel. -/
def PartnerOrder.UpperCut (L : PartnerOrder I m) (μ : Matching n)
    (revealed : Finset (Fin n)) (t : Fin L.length) (b : ℕ) : Prop :=
  b = L.length + 1 ∨ ∃ i : Fin L.length,
    t < i ∧ μ.symm (L.partner i) ∈ revealed ∧ b = i.val + 1

/-- Every exact support index lies strictly between any two valid cuts.
In particular, this applies to the nearest revealed cuts. -/
theorem PartnerOrder.indexSupport_between (L : PartnerOrder I m)
    {μ : Matching n} {revealed : Finset (Fin n)} {t : Fin L.length} {a b : ℕ}
    (hμ : Stable I μ) (ht : L.partner t = μ m)
    (ha : L.LowerCut μ revealed t a) (hb : L.UpperCut μ revealed t b)
    {j : Fin L.length} (hj : j ∈ L.indexSupport μ revealed) :
    a < j.val + 1 ∧ j.val + 1 < b := by
  classical
  have hsupport := (Finset.mem_filter.mp hj).2
  obtain ⟨ν, hν, hνj⟩ := hsupport
  constructor
  · rcases ha with rfl | ⟨i, hit, hi, rfl⟩
    · exact Nat.zero_lt_succ _
    · have hr : I.men m (L.partner i) < I.men m (μ m) := by
        rw [← ht]
        exact L.increasing hit
      have hc := compatible_lower_barrier (L.stable i) hμ hν hi hr
      rw [hνj] at hc
      exact Nat.succ_lt_succ (L.increasing.lt_iff_lt.mp hc)
  · rcases hb with rfl | ⟨i, hti, hi, rfl⟩
    · exact Nat.succ_lt_succ j.isLt
    · have hr : I.men m (μ m) < I.men m (L.partner i) := by
        rw [← ht]
        exact L.increasing hti
      have hc := compatible_upper_barrier (L.stable i) hμ hν hi hr
      rw [hνj] at hc
      exact Nat.succ_lt_succ (L.increasing.lt_iff_lt.mp hc)

/-- Indexing preserves the exact conditional support, including its missing positions. -/
theorem PartnerOrder.image_indexSupport (L : PartnerOrder I m) (μ : Matching n)
    (revealed : Finset (Fin n)) :
    (L.indexSupport μ revealed).image L.partner =
      partnerSupportFinset I μ revealed m := by
  classical
  ext w
  simp only [partnerSupportFinset, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (Finset.mem_filter.mp hj).2
  · intro hw
    obtain ⟨j, rfl⟩ := L.complete w (mem_partnerSupport_stablePair hw)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩

/-- The exact conditional support size is bounded by the interval length.
No hypothesis asserts that every interval position is feasible. -/
theorem PartnerOrder.support_card_le_gap (L : PartnerOrder I m)
    {μ : Matching n} {revealed : Finset (Fin n)} {t : Fin L.length} {a b : ℕ}
    (hμ : Stable I μ) (ht : L.partner t = μ m)
    (ha : L.LowerCut μ revealed t a) (hb : L.UpperCut μ revealed t b) :
    (partnerSupportFinset I μ revealed m).card ≤ b - a - 1 := by
  classical
  have hcard : (partnerSupportFinset I μ revealed m).card =
      (L.indexSupport μ revealed).card := by
    rw [← Finset.card_image_of_injective _ L.injective, L.image_indexSupport]
  rw [hcard]
  have hle : (L.indexSupport μ revealed).card ≤ (Finset.Ioo a b).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin L.length => j.val + 1)
    · intro j hj
      exact Finset.mem_Ioo.mpr (L.indexSupport_between hμ ht ha hb hj)
    · intro i _ j _ hij
      exact Fin.ext (Nat.add_right_cancel hij)
  simpa only [Nat.card_Ioo] using hle

end SmpMax.General

import SmpMax.General.LongDirectionalSaving
import SmpMax.General.GapSides

/-! # Local events describe the two sides of one finite gap -/

namespace SmpMax.General.LongGap

variable {d N : ℕ}

def localIndex (t : Fin d) (hl : 24 ≤ t.val) (hr : t.val + 24 < d)
    (right : Bool) (i : Fin 49) : Fin d :=
  if hi : i.val ≤ 24 then
    if right then ⟨t.val + i.val, by omega⟩ else ⟨t.val - i.val, by omega⟩
  else
    if right then ⟨t.val - (i.val - 24), by omega⟩
    else ⟨t.val + (i.val - 24), by omega⟩

@[simp] theorem localIndex_zero (t : Fin d) (hl : 24 ≤ t.val) (hr : t.val + 24 < d)
    (right : Bool) : localIndex t hl hr right 0 = t := by
  cases right <;> simp [localIndex]

theorem localIndex_injective (t : Fin d) (hl : 24 ≤ t.val) (hr : t.val + 24 < d)
    (right : Bool) : Function.Injective (localIndex t hl hr right) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  cases right <;> simp only [localIndex, Bool.false_eq_true, ↓reduceIte] at h <;>
    split_ifs at h <;> dsimp only at h <;> omega

def localLabels (owner : Fin d → Fin N) (t : Fin d)
    (hl : 24 ≤ t.val) (hr : t.val + 24 < d) (right : Bool) : Fin 49 → Fin N :=
  fun i => owner (localIndex t hl hr right i)

@[simp] theorem localLabels_zero (owner : Fin d → Fin N) (t : Fin d)
    (hl : 24 ≤ t.val) (hr : t.val + 24 < d) (right : Bool) :
    localLabels owner t hl hr right 0 = owner t := by simp [localLabels]

theorem localLabels_injective (owner : Fin d → Fin N) (hinj : Function.Injective owner)
    (t : Fin d) (hl : 24 ≤ t.val) (hr : t.val + 24 < d) (right : Bool) :
    Function.Injective (localLabels owner t hl hr right) :=
  hinj.comp (localIndex_injective t hl hr right)

theorem event_lengths (owner : Fin d → Fin N) (t : Fin d)
    (hl : 24 ≤ t.val) (hr : t.val + 24 < d) (right : Bool)
    {j k : ℕ} (hj : j ≤ 23) (hk : k ≤ 3) (π : Equiv.Perm (Fin N))
    (he : π ∈ oneEvent (localLabels owner t hl hr right) j k hj) :
    (if right then Gap.leftSize (Gap.revealedBy owner π t) t
      else Gap.rightSize (Gap.revealedBy owner π t) t) = j ∧
    k ≤ (if right then Gap.rightSize (Gap.revealedBy owner π t) t
      else Gap.leftSize (Gap.revealedBy owner π t) t) := by
  obtain ⟨hb, hc⟩ := (mem_oneEvent _ π j k hj).mp he
  simp only [localLabels_zero] at hb hc
  have hclear (a : Fin 49) (ha : a ∈ afterIndices j k) :
      localIndex t hl hr right a ∉ Gap.revealedBy owner π t := by
    intro hs
    have hn := hc a ha
    have hy := (Finset.mem_filter.mp hs).2
    exact (not_lt_of_ge hn.le) hy
  have hseen : localIndex t hl hr right (boundary j hj) ∈ Gap.revealedBy owner π t :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at hclear hseen ⊢
    have hleft : ∀ i : Fin d, t.val - k ≤ i.val → i.val < t.val →
        i ∉ Gap.revealedBy owner π t := by
      intro i hi hit
      let a : Fin 49 := ⟨t.val - i.val, by omega⟩
      have ha : a ∈ afterIndices j k := by
        simp only [afterIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        left
        dsimp [a]
        omega
      have heq : localIndex t hl hr false a = i := by
        apply Fin.ext
        simp [localIndex, a, show t.val - i.val ≤ 24 by omega]
        omega
      simpa only [heq] using hclear a ha
    have hright : ∀ i : Fin d, t.val < i.val → i.val ≤ t.val + j →
        i ∉ Gap.revealedBy owner π t := by
      intro i hit hi
      let a : Fin 49 := ⟨i.val - t.val + 24, by omega⟩
      have ha : a ∈ afterIndices j k := by
        simp only [afterIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        right
        dsimp [a]
        omega
      have heq : localIndex t hl hr false a = i := by
        apply Fin.ext
        simp [localIndex, a, show ¬ i.val - t.val + 24 ≤ 24 by omega]
        omega
      simpa only [heq] using hclear a ha
    refine ⟨Gap.rightSize_eq_of_boundary ?_ hseen hright,
      Gap.leftSize_ge_of_clear (by omega) hleft⟩
    simp [localIndex, boundary, show ¬ j + 25 ≤ 24 by omega]
    omega
  · simp only [↓reduceIte] at hclear hseen ⊢
    have hleft : ∀ i : Fin d, t.val - j ≤ i.val → i.val < t.val →
        i ∉ Gap.revealedBy owner π t := by
      intro i hi hit
      let a : Fin 49 := ⟨t.val - i.val + 24, by omega⟩
      have ha : a ∈ afterIndices j k := by
        simp only [afterIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        right
        dsimp [a]
        omega
      have heq : localIndex t hl hr true a = i := by
        apply Fin.ext
        simp [localIndex, a, show ¬ t.val - i.val + 24 ≤ 24 by omega]
        omega
      simpa only [heq] using hclear a ha
    have hright : ∀ i : Fin d, t.val < i.val → i.val ≤ t.val + k →
        i ∉ Gap.revealedBy owner π t := by
      intro i hit hi
      let a : Fin 49 := ⟨i.val - t.val, by omega⟩
      have ha : a ∈ afterIndices j k := by
        simp only [afterIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        left
        dsimp [a]
        omega
      have heq : localIndex t hl hr true a = i := by
        apply Fin.ext
        simp [localIndex, a, show i.val - t.val ≤ 24 by omega]
        omega
      simpa only [heq] using hclear a ha
    refine ⟨Gap.leftSize_eq_of_boundary ?_ hseen hleft,
      Gap.rightSize_ge_of_clear (by omega) hright⟩
    simp [localIndex, boundary, show ¬ j + 25 ≤ 24 by omega]
    omega

def directionalData (owner : Fin d → Fin N) (hinj : Function.Injective owner)
    (t : Fin d) (hl : 24 ≤ t.val) (hr : t.val + 24 < d) (right : Bool)
    (cap : Equiv.Perm (Fin N) → ℕ)
    (hcap : ∀ π, cap π ≤ if right then Gap.rightSize (Gap.revealedBy owner π t) t
      else Gap.leftSize (Gap.revealedBy owner π t) t) : DirectionalData N where
  label := localLabels owner t hl hr right
  injective := localLabels_injective owner hinj t hl hr right
  L := fun π => if right then Gap.leftSize (Gap.revealedBy owner π t) t
    else Gap.rightSize (Gap.revealedBy owner π t) t
  R := fun π => if right then Gap.rightSize (Gap.revealedBy owner π t) t
    else Gap.leftSize (Gap.revealedBy owner π t) t
  cap := cap
  cap_le := hcap
  event_spec := fun _ _ hj hk π he => event_lengths owner t hl hr right hj hk π he

end SmpMax.General.LongGap

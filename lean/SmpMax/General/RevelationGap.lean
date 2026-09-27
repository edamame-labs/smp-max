import SmpMax.General.PartnerIntervals
import Mathlib.Data.Finset.Max

/-!
# Nearest revealed barriers and finite windows

All positions belong to the compressed stable-partner list. Cuts use
shifted positions: the sentinels are `0` and `d + 1`. The gap between
them contains exactly the unrevealed run around the pivot.
-/

namespace SmpMax.General.Gap

variable {d : ℕ}

def lowerCandidates (R : Finset (Fin d)) (t : Fin d) : Finset ℕ :=
  insert 0 ((R.filter (· < t)).image (fun i => i.val + 1))

def upperCandidates (R : Finset (Fin d)) (t : Fin d) : Finset ℕ :=
  insert (d + 1) ((R.filter (t < ·)).image (fun i => i.val + 1))

def lower (R : Finset (Fin d)) (t : Fin d) : ℕ :=
  (lowerCandidates R t).max' (Finset.insert_nonempty _ _)

def upper (R : Finset (Fin d)) (t : Fin d) : ℕ :=
  (upperCandidates R t).min' (Finset.insert_nonempty _ _)

def size (R : Finset (Fin d)) (t : Fin d) : ℕ :=
  upper R t - lower R t - 1

theorem lower_spec (R : Finset (Fin d)) (t : Fin d) :
    lower R t = 0 ∨ ∃ i ∈ R, i < t ∧ lower R t = i.val + 1 := by
  have h := Finset.max'_mem (lowerCandidates R t) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl h
  · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, heq.symm⟩

theorem upper_spec (R : Finset (Fin d)) (t : Fin d) :
    upper R t = d + 1 ∨ ∃ i ∈ R, t < i ∧ upper R t = i.val + 1 := by
  have h := Finset.min'_mem (upperCandidates R t) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl h
  · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, heq.symm⟩

theorem lower_le_pivot (R : Finset (Fin d)) (t : Fin d) : lower R t ≤ t.val := by
  rcases lower_spec R t with h | ⟨i, _, hi, h⟩ <;> simp only [h]
  · exact Nat.zero_le _
  · exact hi

theorem pivot_lt_upper (R : Finset (Fin d)) (t : Fin d) : t.val + 1 < upper R t := by
  rcases upper_spec R t with h | ⟨i, _, hi, h⟩ <;> simp only [h]
  · exact Nat.succ_lt_succ t.isLt
  · exact Nat.succ_lt_succ hi

theorem upper_le_end (R : Finset (Fin d)) (t : Fin d) : upper R t ≤ d + 1 := by
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem revealed_left_le_lower {R : Finset (Fin d)} {t i : Fin d}
    (hi : i ∈ R) (hit : i < t) : i.val + 1 ≤ lower R t := by
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_filter.mpr ⟨hi, hit⟩, rfl⟩)

theorem upper_le_revealed_right {R : Finset (Fin d)} {t i : Fin d}
    (hi : i ∈ R) (hti : t < i) : upper R t ≤ i.val + 1 := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_filter.mpr ⟨hi, hti⟩, rfl⟩)

theorem size_pos (R : Finset (Fin d)) (t : Fin d) : 0 < size R t := by
  have := lower_le_pivot R t
  have := pivot_lt_upper R t
  unfold size
  omega

theorem size_le_length (R : Finset (Fin d)) (t : Fin d) : size R t ≤ d := by
  have := upper_le_end R t
  unfold size
  omega

/-- An interval of k positions contained in the list and containing the pivot. -/
def Window (t : Fin d) (k start : ℕ) : Prop :=
  start ≤ t.val ∧ t.val < start + k ∧ start + k ≤ d

def Clear (R : Finset (Fin d)) (k start : ℕ) : Prop :=
  ∀ i : Fin d, start ≤ i.val → i.val < start + k → i ∉ R

/-- There is no revealed position strictly between the two nearest cuts. -/
theorem clear_between {R : Finset (Fin d)} {t i : Fin d} (ht : t ∉ R)
    (hl : lower R t ≤ i.val) (hu : i.val + 1 < upper R t) : i ∉ R := by
  intro hi
  rcases lt_trichotomy i t with hit | rfl | hti
  · have := revealed_left_le_lower hi hit
    omega
  · exact ht hi
  · have := upper_le_revealed_right hi hti
    omega

/-- Every clear window containing the pivot lies inside the nearest cuts. -/
theorem clear_window_inside {R : Finset (Fin d)} {t : Fin d} {k s : ℕ}
    (hw : Window t k s) (hc : Clear R k s) :
    lower R t ≤ s ∧ s + k < upper R t := by
  have hend := hw.2.2
  constructor
  · rcases lower_spec R t with h | ⟨i, hi, hit, h⟩
    · omega
    · have hn : ¬ s ≤ i.val := fun hsi => hc i hsi (by
        have : i.val < t.val := hit
        exact lt_trans this hw.2.1) hi
      omega
  · rcases upper_spec R t with h | ⟨i, hi, hti, h⟩
    · omega
    · have hn : ¬ i.val < s + k := fun his => hc i (by
        have : t.val < i.val := hti
        exact le_trans hw.1 this.le) his hi
      omega

/-- A gap of length at least k is equivalent to a clear k-window around the pivot. -/
theorem size_ge_iff_window {R : Finset (Fin d)} {t : Fin d} (ht : t ∉ R)
    {k : ℕ} (hk : 0 < k) :
    k ≤ size R t ↔ ∃ s, Window t k s ∧ Clear R k s := by
  constructor
  · intro hgap
    let s := max (lower R t) (t.val + 1 - k)
    have hl := lower_le_pivot R t
    have hu := pivot_lt_upper R t
    have hend := upper_le_end R t
    have hs1 : lower R t ≤ s := le_max_left _ _
    have hs2 : t.val + 1 - k ≤ s := le_max_right _ _
    have hsmax : s = lower R t ∨ s = t.val + 1 - k := max_choice _ _
    have hw : Window t k s := by
      unfold Window
      unfold size at hgap
      rcases hsmax with h | h <;> omega
    have hsu : s + k < upper R t := by
      unfold size at hgap
      rcases hsmax with h | h <;> omega
    refine ⟨s, hw, fun i his hik => clear_between ht (hs1.trans his) ?_⟩
    omega
  · rintro ⟨s, hw, hc⟩
    have := clear_window_inside hw hc
    unfold size
    omega

end SmpMax.General.Gap

namespace SmpMax.General

variable {n : ℕ}

/-- A permutation assigns distinct reveal times to fixed men. -/
def earlierMen (π : Equiv.Perm (Fin n)) (m : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => π u < π m)

def PartnerOrder.revealedPositions {I : Profile n} {m : Fin n}
    (L : PartnerOrder I m) (μ : Matching n) (π : Equiv.Perm (Fin n)) :
    Finset (Fin L.length) :=
  Finset.univ.filter (fun j => μ.symm (L.partner j) ∈ earlierMen π m)

theorem PartnerOrder.pivot_not_revealed {I : Profile n} {m : Fin n}
    (L : PartnerOrder I m) (μ : Matching n) (π : Equiv.Perm (Fin n))
    {t : Fin L.length} (ht : L.partner t = μ m) :
    t ∉ L.revealedPositions μ π := by
  simp [revealedPositions, earlierMen, ht]

/-- The deterministic support bound instantiated with the actual nearest revealed cuts. -/
theorem PartnerOrder.support_card_le_revelationGap {I : Profile n} {m : Fin n}
    (L : PartnerOrder I m) {μ : Matching n} (hμ : Stable I μ)
    (π : Equiv.Perm (Fin n)) {t : Fin L.length} (ht : L.partner t = μ m) :
    (partnerSupportFinset I μ (earlierMen π m) m).card ≤
      Gap.size (L.revealedPositions μ π) t := by
  apply L.support_card_le_gap hμ ht
  · rcases Gap.lower_spec (L.revealedPositions μ π) t with h | ⟨i, hi, hit, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hit, (Finset.mem_filter.mp hi).2, h⟩
  · rcases Gap.upper_spec (L.revealedPositions μ π) t with h | ⟨i, hi, hti, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hti, (Finset.mem_filter.mp hi).2, h⟩

end SmpMax.General

import SmpMax.General.RevelationGap

/-! # Left and right lengths of the same finite revelation gap -/

namespace SmpMax.General.Gap

variable {d : ℕ}

def leftSize (S : Finset (Fin d)) (t : Fin d) : ℕ := t.val - lower S t
def rightSize (S : Finset (Fin d)) (t : Fin d) : ℕ := upper S t - t.val - 2

theorem size_eq_one_add_sides (S : Finset (Fin d)) (t : Fin d) :
    size S t = 1 + leftSize S t + rightSize S t := by
  have := lower_le_pivot S t
  have := pivot_lt_upper S t
  simp only [size, leftSize, rightSize]
  omega

theorem leftSize_le (S : Finset (Fin d)) (t : Fin d) : leftSize S t ≤ t.val :=
  Nat.sub_le _ _

theorem rightSize_le (S : Finset (Fin d)) (t : Fin d) : rightSize S t < d - t.val := by
  have := upper_le_end S t
  have := t.isLt
  unfold rightSize
  omega

theorem leftSize_ge_of_clear {S : Finset (Fin d)} {t : Fin d} {k : ℕ}
    (hk : k ≤ t.val) (hc : ∀ i : Fin d, t.val - k ≤ i.val → i.val < t.val → i ∉ S) :
    k ≤ leftSize S t := by
  rcases lower_spec S t with h | ⟨i, hi, hit, h⟩
  · unfold leftSize
    omega
  · have hn : ¬ t.val - k ≤ i.val := fun he => hc i he hit hi
    unfold leftSize
    omega

theorem rightSize_ge_of_clear {S : Finset (Fin d)} {t : Fin d} {k : ℕ}
    (hk : t.val + k < d) (hc : ∀ i : Fin d, t.val < i.val → i.val ≤ t.val + k → i ∉ S) :
    k ≤ rightSize S t := by
  rcases upper_spec S t with h | ⟨i, hi, hti, h⟩
  · unfold rightSize
    omega
  · have hn : ¬ i.val ≤ t.val + k := fun he => hc i hti he hi
    unfold rightSize
    omega

theorem leftSize_eq_of_boundary {S : Finset (Fin d)} {t b : Fin d} {j : ℕ}
    (hb : b.val + j + 1 = t.val) (hs : b ∈ S)
    (hc : ∀ i : Fin d, t.val - j ≤ i.val → i.val < t.val → i ∉ S) :
    leftSize S t = j := by
  have hlo := leftSize_ge_of_clear (by omega : j ≤ t.val) hc
  have hup := revealed_left_le_lower (t := t) hs (by change b.val < t.val; omega)
  unfold leftSize at *
  omega

theorem rightSize_eq_of_boundary {S : Finset (Fin d)} {t b : Fin d} {j : ℕ}
    (hb : b.val = t.val + j + 1) (hs : b ∈ S)
    (hc : ∀ i : Fin d, t.val < i.val → i.val ≤ t.val + j → i ∉ S) :
    rightSize S t = j := by
  have hlo := rightSize_ge_of_clear (by have := b.isLt; omega : t.val + j < d) hc
  have hup := upper_le_revealed_right (t := t) hs (by change t.val < b.val; omega)
  unfold rightSize at *
  omega

end SmpMax.General.Gap

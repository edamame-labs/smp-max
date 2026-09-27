import SmpMax.General.PartnerIntervals
import Mathlib.Data.Finset.Lattice.Fold

/-! # Exact support extrema and their interval cardinality bound -/

namespace SmpMax.General.SupportCaps

variable {d : ℕ}

def left (S : Finset (Fin d)) (t : Fin d) : ℕ := S.sup (fun j => t.val - j.val)
def right (S : Finset (Fin d)) (t : Fin d) : ℕ := S.sup (fun j => j.val - t.val)

theorem left_le_pivot (S : Finset (Fin d)) (t : Fin d) : left S t ≤ t.val := by
  exact Finset.sup_le (fun _ _ => Nat.sub_le _ _)

theorem right_lt_end (S : Finset (Fin d)) (t : Fin d) : right S t < d - t.val := by
  have h : right S t ≤ d - t.val - 1 := by
    apply Finset.sup_le
    intro j _
    have := j.isLt
    omega
  have := t.isLt
  omega

theorem mem_bounds {S : Finset (Fin d)} {t j : Fin d} (hj : j ∈ S) :
    t.val - left S t ≤ j.val ∧ j.val ≤ t.val + right S t := by
  have hl : t.val - j.val ≤ left S t := Finset.le_sup (f := fun j => t.val - j.val) hj
  have hr : j.val - t.val ≤ right S t := Finset.le_sup (f := fun j => j.val - t.val) hj
  omega

theorem card_le (S : Finset (Fin d)) (t : Fin d) : S.card ≤ 1 + left S t + right S t := by
  have hb := left_le_pivot S t
  have hi : S.card ≤ (Finset.Icc (t.val - left S t) (t.val + right S t)).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin d => j.val)
    · intro j hj
      exact Finset.mem_Icc.mpr (mem_bounds hj)
    · intro i _ j _ he
      exact Fin.ext he
  rw [Nat.card_Icc] at hi
  omega

theorem left_le {S : Finset (Fin d)} {t : Fin d} {q : ℕ}
    (h : ∀ j ∈ S, t.val ≤ j.val + q) : left S t ≤ q := by
  exact Finset.sup_le (fun j hj => by have := h j hj; omega)

theorem right_le {S : Finset (Fin d)} {t : Fin d} {q : ℕ}
    (h : ∀ j ∈ S, j.val ≤ t.val + q) : right S t ≤ q := by
  exact Finset.sup_le (fun j hj => by have := h j hj; omega)

end SmpMax.General.SupportCaps

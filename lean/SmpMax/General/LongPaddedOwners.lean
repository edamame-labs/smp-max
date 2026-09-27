import SmpMax.General.GapSides
import SmpMax.General.ExtendedRevelation

/-!
# Forty-eight auxiliary owner labels, without adding matching coordinates

Every ordered owner list receives twenty-four fresh labels on each side. The
same forty-eight labels are reused for different men. Only injectivity within
each list is needed by the gap estimate.
-/

namespace SmpMax.General.LongPadded

variable {d n : ℕ}

def realLabel (u : Fin n) : Fin (n + 48) := ⟨u.val, by omega⟩
def position (i : Fin d) : Fin (d + 48) := ⟨i.val + 24, by omega⟩

theorem realLabel_injective : Function.Injective (realLabel (n := n)) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (n + 48) => x.val) h)

theorem position_injective : Function.Injective (position (d := d)) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [position] at this
  omega

def owner (f : Fin d → Fin n) (i : Fin (d + 48)) : Fin (n + 48) :=
  if hleft : i.val < 24 then ⟨n + i.val, by omega⟩
  else if hreal : i.val < d + 24 then realLabel (f ⟨i.val - 24, by omega⟩)
  else ⟨n + 24 + (i.val - (d + 24)), by omega⟩

@[simp] theorem owner_position (f : Fin d → Fin n) (i : Fin d) :
    owner f (position i) = realLabel (f i) := by
  simp [owner, position, show i.val < d from i.isLt]

theorem owner_injective (f : Fin d → Fin n) (hinj : Function.Injective f) :
    Function.Injective (owner f) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [owner] at hij hv
  split_ifs at hij hv with hi hi' hj hj' <;>
    simp only [realLabel, Fin.val_mk] at hv
  all_goals first
    | (apply Fin.ext; omega)
    | (have he : (⟨i.val - 24, by omega⟩ : Fin d) = ⟨j.val - 24, by omega⟩ :=
        hinj (realLabel_injective hij)
       have he' := congrArg Fin.val he
       apply Fin.ext
       dsimp only at he'
       omega)

theorem position_left (i : Fin d) : 24 ≤ (position i).val := by simp [position]
theorem position_right (i : Fin d) : (position i).val + 24 < d + 48 := by
  simp only [position]
  omega

def earlier (π : Equiv.Perm (Fin (n + 48))) (m : Fin n) : Finset (Fin n) :=
  earlierByRank (fun u => π (realLabel u)) m

@[simp] theorem mem_earlier (π : Equiv.Perm (Fin (n + 48))) (m u : Fin n) :
    u ∈ earlier π m ↔ π (realLabel u) < π (realLabel m) := by
  simp [earlier, earlierByRank]

end SmpMax.General.LongPadded

import SmpMax.General.GapSides
import SmpMax.General.ExtendedRevelation

/-!
# Six auxiliary owner labels, without adding matching coordinates

Every ordered owner list receives three fresh labels on each side. The
same six labels are reused for different men. Only injectivity within
each list is needed by the gap estimate.
-/

namespace SmpMax.General.Padded

variable {d n : ℕ}

def realLabel (u : Fin n) : Fin (n + 6) := ⟨u.val, by omega⟩
def position (i : Fin d) : Fin (d + 6) := ⟨i.val + 3, by omega⟩

theorem realLabel_injective : Function.Injective (realLabel (n := n)) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (n + 6) => x.val) h)

theorem position_injective : Function.Injective (position (d := d)) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [position] at this
  omega

def owner (f : Fin d → Fin n) (i : Fin (d + 6)) : Fin (n + 6) :=
  if hleft : i.val < 3 then ⟨n + i.val, by omega⟩
  else if hreal : i.val < d + 3 then realLabel (f ⟨i.val - 3, by omega⟩)
  else ⟨n + 3 + (i.val - (d + 3)), by omega⟩

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
    | (have he : (⟨i.val - 3, by omega⟩ : Fin d) = ⟨j.val - 3, by omega⟩ :=
        hinj (realLabel_injective hij)
       have he' := congrArg Fin.val he
       apply Fin.ext
       dsimp only at he'
       omega)

theorem position_left (i : Fin d) : 3 ≤ (position i).val := by simp [position]
theorem position_right (i : Fin d) : (position i).val + 3 < d + 6 := by
  simp only [position]
  omega

def earlier (π : Equiv.Perm (Fin (n + 6))) (m : Fin n) : Finset (Fin n) :=
  earlierByRank (fun u => π (realLabel u)) m

@[simp] theorem mem_earlier (π : Equiv.Perm (Fin (n + 6))) (m u : Fin n) :
    u ∈ earlier π m ↔ π (realLabel u) < π (realLabel m) := by
  simp [earlier, earlierByRank]

end SmpMax.General.Padded

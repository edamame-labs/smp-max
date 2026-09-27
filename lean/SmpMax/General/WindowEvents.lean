import SmpMax.General.RevelationGap
import SmpMax.General.PermutationCounting
import Mathlib.Data.Nat.Find

/-!
# A finite event cover for a long revelation gap

A long gap contains a clear window. The leftmost clear window is either
the first possible window or has a revealed position immediately to its
left. Thus one first-position event and at most k-1 first-two-position
events suffice to bound the gap tail. The proof only needs a cover;
disjointness is not assumed in the later union bound.
-/

namespace SmpMax.General.Gap

variable {d n : ℕ}

def firstStart (t : Fin d) (k : ℕ) : ℕ := t.val + 1 - k

def lastStart (t : Fin d) (k : ℕ) : ℕ := min t.val (d - k)

def laterStarts (t : Fin d) (k : ℕ) : Finset ℕ :=
  Finset.Ioc (firstStart t k) (lastStart t k)

theorem first_window (t : Fin d) {k : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    Window t k (firstStart t k) := by
  have := t.isLt
  unfold Window firstStart
  omega

theorem window_of_mem_later {t : Fin d} {k s : ℕ} (hs : s ∈ laterStarts t k) :
    Window t k s := by
  have h := Finset.mem_Ioc.mp hs
  unfold firstStart lastStart at h
  unfold Window
  omega

theorem laterStarts_card_le (t : Fin d) {k : ℕ} (hk : 0 < k) :
    (laterStarts t k).card ≤ k - 1 := by
  simp only [laterStarts, Nat.card_Ioc, firstStart, lastStart]
  omega

/-- The leftmost clear window produces the event cover used in the tail estimate. -/
theorem long_gap_cover {R : Finset (Fin d)} {t : Fin d} (ht : t ∉ R)
    {k : ℕ} (hk : 0 < k) (hgap : k ≤ size R t) :
    Clear R k (firstStart t k) ∨
      ∃ s ∈ laterStarts t k, Clear R k s ∧
        ∃ i : Fin d, i.val + 1 = s ∧ i ∈ R := by
  classical
  have hex := (size_ge_iff_window ht hk).mp hgap
  let s := Nat.find hex
  have hwc : Window t k s ∧ Clear R k s := Nat.find_spec hex
  have hst := hwc.1.1
  have htk := hwc.1.2.1
  have hkd := hwc.1.2.2
  have hmin : firstStart t k ≤ s := by unfold firstStart; omega
  by_cases heq : s = firstStart t k
  · exact Or.inl (heq ▸ hwc.2)
  have hlt : firstStart t k < s := lt_of_le_of_ne hmin (Ne.symm heq)
  have hspos : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hsp : Window t k (s - 1) := by
    unfold Window firstStart at *
    omega
  have hpred : ¬ Clear R k (s - 1) := by
    intro hc
    exact Nat.find_min hex (show s - 1 < Nat.find hex by change s - 1 < s; omega)
      ⟨hsp, hc⟩
  have hip : s - 1 < d := by omega
  let i : Fin d := ⟨s - 1, hip⟩
  have hir : i ∈ R := by
    by_contra hn
    apply hpred
    intro j hsj hjk hj
    by_cases hji : j = i
    · exact hn (hji ▸ hj)
    · have hne : j.val ≠ s - 1 := fun h => hji (Fin.ext h)
      exact hwc.2 j (by omega) (by omega) hj
  refine Or.inr ⟨s, ?_, hwc.2, i, ?_, hir⟩
  · apply Finset.mem_Ioc.mpr
    unfold lastStart
    exact ⟨hlt, by omega⟩
  · change (s - 1) + 1 = s
    omega

def positions (d k s : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun i => s ≤ i.val ∧ i.val < s + k)

theorem positions_card {k s : ℕ} (hsk : s + k ≤ d) : (positions d k s).card = k := by
  symm
  calc
    k = (Finset.univ : Finset (Fin k)).card := by simp
    _ = _ := by
      apply Finset.card_bij (fun j _ => (⟨s + j.val, by omega⟩ : Fin d))
      · intro j _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
      · intro i _ j _ hij
        apply Fin.ext
        have := congrArg Fin.val hij
        dsimp at this
        omega
      · intro j hj
        obtain ⟨hsj, hjk⟩ := (Finset.mem_filter.mp hj).2
        refine ⟨⟨j.val - s, by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        dsimp
        omega

theorem pivot_mem_positions {t : Fin d} {k s : ℕ} (hw : Window t k s) :
    t ∈ positions d k s :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1, hw.2.1⟩

def revealedBy (owner : Fin d → Fin n) (π : Equiv.Perm (Fin n)) (t : Fin d) :
    Finset (Fin d) :=
  Finset.univ.filter (fun j => π (owner j) < π (owner t))

theorem pivot_not_mem_revealedBy (owner : Fin d → Fin n)
    (π : Equiv.Perm (Fin n)) (t : Fin d) : t ∉ revealedBy owner π t := by
  simp [revealedBy]

/-- A clear window says exactly that the pivot's owner is first among its owners. -/
theorem clear_iff_isFirst (owner : Fin d → Fin n) (π : Equiv.Perm (Fin n))
    {t : Fin d} {k s : ℕ} (hw : Window t k s) :
    Clear (revealedBy owner π t) k s ↔
      PermutationCounting.IsFirst π ((positions d k s).image owner) (owner t) := by
  constructor
  · intro hc
    refine ⟨Finset.mem_image_of_mem owner (pivot_mem_positions hw), ?_⟩
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hsj, hjk⟩ := (Finset.mem_filter.mp hj).2
    apply le_of_not_gt
    intro h
    exact hc j hsj hjk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro h j hsj hjk hj
    have hmem := Finset.mem_image_of_mem owner
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hsj, hjk⟩ : j ∈ positions d k s)
    exact (not_lt_of_ge (h.2 _ hmem)) (Finset.mem_filter.mp hj).2

end SmpMax.General.Gap

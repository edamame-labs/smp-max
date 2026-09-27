import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact counts of first and second positions in a random permutation

Permutations assign distinct ranks to fixed participants. Relabeling
participants by a transposition is a bijection of the sample space.
The cardinality identities below do not assume a probability law for a
restricted permutation; they establish the required symmetry directly.
-/

namespace SmpMax.General.PermutationCounting

variable {n : ℕ}

def IsFirst (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (a : Fin n) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, π a ≤ π b

noncomputable def firstFilter (T : Finset (Equiv.Perm (Fin n)))
    (S : Finset (Fin n)) (a : Fin n) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact T.filter (fun π => IsFirst π S a)

theorem mem_firstFilter {T : Finset (Equiv.Perm (Fin n))}
    {S : Finset (Fin n)} {a : Fin n} {π : Equiv.Perm (Fin n)} :
    π ∈ firstFilter T S a ↔ π ∈ T ∧ IsFirst π S a := by
  classical
  exact Finset.mem_filter

theorem exists_isFirst (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hS : S.Nonempty) : ∃ a, IsFirst π S a :=
  S.exists_min_image π hS

theorem IsFirst.unique {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    {a b : Fin n} (ha : IsFirst π S a) (hb : IsFirst π S b) : a = b :=
  π.injective (le_antisymm (ha.2 b hb.1) (hb.2 a ha.1))

theorem swap_mem_iff {S : Finset (Fin n)} {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (x : Fin n) : x ∈ S ↔ Equiv.swap a b x ∈ S := by
  by_cases hxa : x = a
  · subst x
    simp [ha, hb]
  by_cases hxb : x = b
  · subst x
    simp [ha, hb]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem isFirst_precomp (e π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hS : ∀ x, x ∈ S ↔ e x ∈ S) (a : Fin n) :
    IsFirst (e.trans π) S a ↔ IsFirst π S (e a) := by
  constructor
  · intro h
    refine ⟨(hS a).mp h.1, fun b hb => ?_⟩
    have hmem : e.symm b ∈ S := (hS _).mpr (by simpa using hb)
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using h.2 _ hmem
  · intro h
    exact ⟨(hS a).mpr h.1, fun b hb => h.2 (e b) ((hS b).mp hb)⟩

/-- Relabeling two eligible participants equates their first-position counts. -/
theorem firstFilter_card_eq {T : Finset (Equiv.Perm (Fin n))}
    {S : Finset (Fin n)} {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (hT : ∀ π, π ∈ T ↔ (Equiv.swap a b).trans π ∈ T) :
    (firstFilter T S a).card = (firstFilter T S b).card := by
  classical
  let F := fun π : Equiv.Perm (Fin n) => (Equiv.swap a b).trans π
  have hinv (π : Equiv.Perm (Fin n)) : F (F π) = π := by
    apply Equiv.ext
    intro x
    simp [F, Equiv.trans_apply]
  have hfirst (π : Equiv.Perm (Fin n)) : IsFirst π S a ↔ IsFirst (F π) S b := by
    simpa only [F, Equiv.swap_apply_right] using
      (isFirst_precomp (Equiv.swap a b) π S (swap_mem_iff ha hb) b).symm
  have hmap : ∀ π, π ∈ firstFilter T S a ↔ F π ∈ firstFilter T S b := by
    intro π
    rw [mem_firstFilter, mem_firstFilter, hT π, hfirst π]
  apply Finset.card_nbij' F F
  · intro π hπ
    exact (hmap π).mp hπ
  · intro π hπ
    apply (hmap (F π)).mpr
    rw [hinv]
    exact hπ
  · intro π _
    exact hinv π
  · intro π _
    exact hinv π

/-- The first-position events partition any finite collection of permutations. -/
theorem card_eq_sum_firstFilter (T : Finset (Equiv.Perm (Fin n)))
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    T.card = ∑ a ∈ S, (firstFilter T S a).card := by
  classical
  let winner := fun π : Equiv.Perm (Fin n) => Classical.choose (exists_isFirst π S hS)
  have hw (π : Equiv.Perm (Fin n)) : IsFirst π S (winner π) :=
    Classical.choose_spec (exists_isFirst π S hS)
  have heq (a : Fin n) : T.filter (fun π => winner π = a) = firstFilter T S a := by
    ext π
    rw [Finset.mem_filter, mem_firstFilter]
    constructor
    · rintro ⟨hπ, h⟩
      exact ⟨hπ, h ▸ hw π⟩
    · rintro ⟨hπ, h⟩
      exact ⟨hπ, (hw π).unique h⟩
  have h := Finset.card_eq_sum_card_fiberwise (s := T) (t := S)
    (f := winner) (fun π _ => (hw π).1)
  simpa only [heq] using h

/-- In any collection invariant under the relevant swaps, each first event
has exactly one |S|-th of the collection's cardinality. -/
theorem card_mul_firstFilter {T : Finset (Equiv.Perm (Fin n))}
    {S : Finset (Fin n)} {a : Fin n} (ha : a ∈ S)
    (hT : ∀ b ∈ S, ∀ π, π ∈ T ↔ (Equiv.swap a b).trans π ∈ T) :
    S.card * (firstFilter T S a).card = T.card := by
  rw [card_eq_sum_firstFilter T S ⟨a, ha⟩]
  calc
    _ = ∑ _b ∈ S, (firstFilter T S a).card := by simp
    _ = _ := Finset.sum_congr rfl fun b hb => firstFilter_card_eq ha hb (hT b hb)

theorem card_mul_first (S : Finset (Fin n)) {a : Fin n} (ha : a ∈ S) :
    S.card * (firstFilter Finset.univ S a).card = Fintype.card (Equiv.Perm (Fin n)) := by
  simpa only [Finset.card_univ] using
    card_mul_firstFilter (T := Finset.univ) ha (fun _ _ _ => by simp)

/-- Exact count for a designated first participant followed by a designated second. -/
theorem card_mul_first_two (S : Finset (Fin n)) {a b : Fin n}
    (ha : a ∈ S) (hb : b ∈ S.erase a) :
    S.card * (S.erase a).card *
      (firstFilter (firstFilter Finset.univ S a) (S.erase a) b).card =
        Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hsecond := card_mul_firstFilter (T := firstFilter Finset.univ S a) hb
    (fun c hc π => by
      rw [mem_firstFilter, mem_firstFilter]
      simp only [Finset.mem_univ, true_and]
      have hS := swap_mem_iff (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hc).2
      have hfix : Equiv.swap b c a = a := Equiv.swap_apply_of_ne_of_ne
        (Finset.mem_erase.mp hb).1.symm (Finset.mem_erase.mp hc).1.symm
      simpa only [hfix] using (isFirst_precomp (Equiv.swap b c) π S hS a).symm)
  rw [mul_assoc, hsecond]
  exact card_mul_first S ha

end SmpMax.General.PermutationCounting

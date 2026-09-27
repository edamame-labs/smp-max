import SmpMax.General.PermutationCounting
import SmpMax.General.FiniteProbability
import Mathlib.Tactic.Ring

/-!
# Exact relative-order probabilities with up to two earlier labels

The sample space is the full permutation group on fixed labels. Auxiliary
labels are allowed: no matching interpretation or independence is assumed.
-/

namespace SmpMax.General.PermutationCounting

open FiniteProbability

variable {n : ℕ}

theorem card_mul_first_three (S : Finset (Fin n)) {a b c : Fin n}
    (ha : a ∈ S) (hb : b ∈ S.erase a) (hc : c ∈ (S.erase a).erase b) :
    S.card * (S.erase a).card * ((S.erase a).erase b).card *
      (firstFilter (firstFilter (firstFilter Finset.univ S a) (S.erase a) b)
        ((S.erase a).erase b) c).card = Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hthird := card_mul_firstFilter
    (T := firstFilter (firstFilter Finset.univ S a) (S.erase a) b) hc
    (fun d hd π => by
      have hca := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
      have hcb := (Finset.mem_erase.mp hc).1
      have hda := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
      have hdb := (Finset.mem_erase.mp hd).1
      have hfixa : Equiv.swap c d a = a :=
        Equiv.swap_apply_of_ne_of_ne hca.symm hda.symm
      have hfixb : Equiv.swap c d b = b :=
        Equiv.swap_apply_of_ne_of_ne hcb.symm hdb.symm
      have hS := swap_mem_iff
        (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
        (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).2
      have hSa := swap_mem_iff (Finset.mem_erase.mp hc).2 (Finset.mem_erase.mp hd).2
      simp only [mem_firstFilter, Finset.mem_univ, true_and]
      rw [isFirst_precomp _ _ S hS, isFirst_precomp _ _ (S.erase a) hSa,
        hfixa, hfixb])
  rw [mul_assoc (S.card * _), hthird]
  exact card_mul_first_two S ha hb

noncomputable def firstTwo (S : Finset (Fin n)) (a m : Fin n) :
    Finset (Equiv.Perm (Fin n)) :=
  firstFilter (firstFilter Finset.univ S a) (S.erase a) m

noncomputable def firstThree (S : Finset (Fin n)) (a b m : Fin n) :
    Finset (Equiv.Perm (Fin n)) :=
  firstFilter (firstFilter (firstFilter Finset.univ S a) (S.erase a) b)
    ((S.erase a).erase b) m

theorem probability_firstTwo (S : Finset (Fin n)) {a m : Fin n}
    (ha : a ∈ S) (hm : m ∈ S.erase a) :
    probability (firstTwo S a m) = 1 / ((S.card : ℝ) * (S.card - 1)) := by
  have hs : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  have ht : 0 < (S.erase a).card := Finset.card_pos.mpr ⟨m, hm⟩
  have h := probability_eq_inv_of_mul_card (firstTwo S a m) (Nat.mul_pos hs ht)
    (card_mul_first_two S ha hm)
  rw [Nat.cast_mul, Finset.card_erase_of_mem ha, Nat.cast_sub (by omega), Nat.cast_one] at h
  exact h

theorem probability_firstThree (S : Finset (Fin n)) {a b m : Fin n}
    (ha : a ∈ S) (hb : b ∈ S.erase a) (hm : m ∈ (S.erase a).erase b) :
    probability (firstThree S a b m) =
      1 / ((S.card : ℝ) * (S.card - 1) * (S.card - 2)) := by
  have hs : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  have ht : 0 < (S.erase a).card := Finset.card_pos.mpr ⟨b, hb⟩
  have hu : 0 < ((S.erase a).erase b).card := Finset.card_pos.mpr ⟨m, hm⟩
  have h := probability_eq_inv_of_mul_card (firstThree S a b m)
    (Nat.mul_pos (Nat.mul_pos hs ht) hu) (card_mul_first_three S ha hb hm)
  rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha] at h
  have hh : 2 ≤ S.card := by
    rw [Finset.card_erase_of_mem ha] at ht
    omega
  rw [Nat.sub_sub, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (by omega), Nat.cast_sub hh] at h
  norm_num at h ⊢
  exact h

theorem mem_firstTwo_iff {S : Finset (Fin n)} {a m : Fin n}
    (ha : a ∈ S) (hm : m ∈ S.erase a) (π : Equiv.Perm (Fin n)) :
    π ∈ firstTwo S a m ↔ π a < π m ∧ ∀ x ∈ S.erase a |>.erase m, π m < π x := by
  classical
  have hma := (Finset.mem_erase.mp hm).1
  simp only [firstTwo, mem_firstFilter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    refine ⟨lt_of_le_of_ne (hfirst.2 m (Finset.mem_erase.mp hm).2)
      (fun h => hma (π.injective h).symm), ?_⟩
    intro x hx
    exact lt_of_le_of_ne (hsecond.2 x (Finset.mem_erase.mp hx).2)
      (fun h => (Finset.mem_erase.mp hx).1 (π.injective h).symm)
  · rintro ⟨ham, hafter⟩
    refine ⟨⟨ha, ?_⟩, ⟨hm, ?_⟩⟩
    · intro x hx
      by_cases hxa : x = a
      · simp [hxa]
      by_cases hxm : x = m
      · simpa [hxm] using ham.le
      exact (ham.trans (hafter x (by simp [hx, hxa, hxm]))).le
    · intro x hx
      by_cases hxm : x = m
      · simp [hxm]
      exact (hafter x (Finset.mem_erase.mpr ⟨hxm, hx⟩)).le

theorem mem_firstThree_iff {S : Finset (Fin n)} {a b m : Fin n}
    (ha : a ∈ S) (hb : b ∈ S.erase a) (hm : m ∈ (S.erase a).erase b)
    (π : Equiv.Perm (Fin n)) :
    π ∈ firstThree S a b m ↔
      π a < π b ∧ π b < π m ∧
        ∀ x ∈ ((S.erase a).erase b).erase m, π m < π x := by
  classical
  have hba := (Finset.mem_erase.mp hb).1
  have hmb := (Finset.mem_erase.mp hm).1
  change (π ∈ firstFilter (firstTwo S a b) ((S.erase a).erase b) m) ↔ _
  rw [mem_firstFilter]
  rw [mem_firstTwo_iff ha hb]
  constructor
  · rintro ⟨⟨hab, hbafter⟩, hmfirst⟩
    refine ⟨hab, hbafter m hm, ?_⟩
    intro x hx
    exact lt_of_le_of_ne (hmfirst.2 x (Finset.mem_erase.mp hx).2)
      (fun h => (Finset.mem_erase.mp hx).1 (π.injective h).symm)
  · rintro ⟨hab, hbm, hafter⟩
    refine ⟨⟨hab, ?_⟩, ⟨hm, ?_⟩⟩
    · intro x hx
      by_cases hxm : x = m
      · simpa [hxm] using hbm
      exact hbm.trans (hafter x (Finset.mem_erase.mpr ⟨hxm, hx⟩))
    · intro x hx
      by_cases hxm : x = m
      · simp [hxm]
      exact (hafter x (Finset.mem_erase.mpr ⟨hxm, hx⟩)).le

noncomputable def beforeOne (a m : Fin n) (A : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun π => π a < π m ∧ ∀ x ∈ A, π m < π x)

noncomputable def beforeTwo (a b m : Fin n) (A : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter
    (fun π => π a < π m ∧ π b < π m ∧ ∀ x ∈ A, π m < π x)

theorem probability_beforeOne {a m : Fin n} {A : Finset (Fin n)}
    (ham : a ≠ m) (ha : a ∉ A) (hm : m ∉ A) :
    probability (beforeOne a m A) =
      1 / (((A.card : ℝ) + 2) * (A.card + 1)) := by
  classical
  let S := insert a (insert m A)
  have ham' : m ∈ S.erase a := by simp [S, ham.symm]
  have hrest : (S.erase a).erase m = A := by
    ext x
    simp [S]
    grind
  have he : beforeOne a m A = firstTwo S a m := by
    ext π
    rw [mem_firstTwo_iff (by simp [S]) ham', hrest]
    simp [beforeOne]
  have hcard : S.card = A.card + 2 := by simp [S, ha, hm, ham]
  rw [he, probability_firstTwo S (by simp [S]) ham', hcard]
  push_cast
  congr 2; ring

theorem probability_beforeTwo {a b m : Fin n} {A : Finset (Fin n)}
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m)
    (ha : a ∉ A) (hb : b ∉ A) (hm : m ∉ A) :
    probability (beforeTwo a b m A) =
      2 / (((A.card : ℝ) + 3) * (A.card + 2) * (A.card + 1)) := by
  classical
  let S := insert a (insert b (insert m A))
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S.erase a := by simp [S, hab.symm]
  have hmS : m ∈ (S.erase a).erase b := by simp [S, ham.symm, hbm.symm]
  have hbS' : b ∈ S := by simp [S]
  have haS' : a ∈ S.erase b := by simp [S, hab]
  have hmS' : m ∈ (S.erase b).erase a := by simp [S, ham.symm, hbm.symm]
  have hrest : ((S.erase a).erase b).erase m = A := by
    ext x
    simp [S]
    grind
  have hrest' : ((S.erase b).erase a).erase m = A := by
    ext x
    simp [S]
    grind
  have he : beforeTwo a b m A = firstThree S a b m ∪ firstThree S b a m := by
    ext π
    rw [Finset.mem_union, mem_firstThree_iff haS hbS hmS,
      mem_firstThree_iff hbS' haS' hmS', hrest, hrest']
    simp only [beforeTwo, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : π a ≠ π b := fun h => hab (π.injective h)
    constructor
    · rintro ⟨ham', hbm', hafter⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h, hbm', hafter⟩
      · exact Or.inr ⟨h, ham', hafter⟩
    · rintro (⟨hab', hbm', hafter⟩ | ⟨hba', ham', hafter⟩)
      · exact ⟨hab'.trans hbm', hbm', hafter⟩
      · exact ⟨ham', hba'.trans ham', hafter⟩
  have hd : Disjoint (firstThree S a b m) (firstThree S b a m) := by
    apply Finset.disjoint_left.mpr
    intro π hπ hπ'
    have hh := (mem_firstThree_iff haS hbS hmS π).mp hπ
    have hh' := (mem_firstThree_iff hbS' haS' hmS' π).mp hπ'
    exact (not_lt_of_ge hh.1.le) hh'.1
  have hcard : S.card = A.card + 3 := by simp [S, ha, hb, hm, hab, ham, hbm]
  rw [he]
  have hu : probability (firstThree S a b m ∪ firstThree S b a m) =
      probability (firstThree S a b m) + probability (firstThree S b a m) := by
    simp only [probability, Finset.card_union_of_disjoint hd, Nat.cast_add, add_div]
  rw [hu, probability_firstThree S haS hbS hmS,
    probability_firstThree S hbS' haS' hmS', hcard]
  push_cast
  ring

end SmpMax.General.PermutationCounting

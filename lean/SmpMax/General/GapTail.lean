import SmpMax.General.WindowEvents
import SmpMax.General.FiniteProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A uniform tail bound for the revelation gap

The owner map is fixed and injective. Permutations range over all men,
not over a matching-dependent or truncated sample space. The event
cover and exact first/second-position counts give Pr(K >= k) <= 2/(k+1).
-/

namespace SmpMax.General.Gap

open PermutationCounting FiniteProbability

variable {d n : ℕ}

noncomputable def clearEvent (owner : Fin d → Fin n) (t : Fin d) (k s : ℕ) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun π => Clear (revealedBy owner π t) k s)

noncomputable def newWindowEvent (owner : Fin d → Fin n) (t : Fin d) (k s : ℕ) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun π => Clear (revealedBy owner π t) k s ∧
    ∃ i : Fin d, i.val + 1 = s ∧ i ∈ revealedBy owner π t)

noncomputable def tailEvent (owner : Fin d → Fin n) (t : Fin d) (k : ℕ) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun π => k ≤ size (revealedBy owner π t) t)

theorem clearEvent_eq (owner : Fin d → Fin n) {t : Fin d} {k s : ℕ}
    (hw : Window t k s) :
    clearEvent owner t k s =
      firstFilter Finset.univ ((positions d k s).image owner) (owner t) := by
  classical
  ext π
  simp only [clearEvent, Finset.mem_filter, Finset.mem_univ, true_and, mem_firstFilter]
  exact clear_iff_isFirst owner π hw

theorem probability_clearEvent (owner : Fin d → Fin n) (hinj : Function.Injective owner)
    {t : Fin d} {k s : ℕ} (hw : Window t k s) :
    probability (clearEvent owner t k s) = 1 / (k : ℝ) := by
  have hk : 0 < k := by have := hw.1; have := hw.2.1; omega
  have hcard : ((positions d k s).image owner).card = k := by
    rw [Finset.card_image_of_injective _ hinj, positions_card hw.2.2]
  rw [clearEvent_eq owner hw]
  apply probability_eq_inv_of_mul_card _ hk
  have hcount := card_mul_first _ (Finset.mem_image_of_mem owner (pivot_mem_positions hw))
  rwa [hcard] at hcount

theorem predecessor_not_mem (owner : Fin d → Fin n) (hinj : Function.Injective owner)
    {k s : ℕ} {i : Fin d} (hi : i.val + 1 = s) :
    owner i ∉ (positions d k s).image owner := by
  intro h
  obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp h
  have hji := hinj hij
  subst j
  have := (Finset.mem_filter.mp hj).2.1
  omega

/-- Clear window plus a revealed predecessor is exactly a specified first pair. -/
theorem newWindowEvent_eq (owner : Fin d → Fin n) (hinj : Function.Injective owner)
    {t : Fin d} {k s : ℕ} (hw : Window t k s) {i : Fin d} (hi : i.val + 1 = s) :
    newWindowEvent owner t k s =
      firstFilter (firstFilter Finset.univ
        (insert (owner i) ((positions d k s).image owner)) (owner i))
        ((positions d k s).image owner) (owner t) := by
  classical
  let W := (positions d k s).image owner
  have ht : owner t ∈ W := Finset.mem_image_of_mem owner (pivot_mem_positions hw)
  have hnot : owner i ∉ W := predecessor_not_mem owner hinj hi
  ext π
  simp only [newWindowEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_firstFilter]
  constructor
  · rintro ⟨hc, j, hj, hrev⟩
    have hji : j = i := Fin.ext (by omega)
    subst j
    have hlt : π (owner i) < π (owner t) := (Finset.mem_filter.mp hrev).2
    have hf := (clear_iff_isFirst owner π hw).mp hc
    refine ⟨⟨Finset.mem_insert_self _ _, ?_⟩, hf⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · exact hlt.le.trans (hf.2 b hb)
  · rintro ⟨ha, hb⟩
    refine ⟨(clear_iff_isFirst owner π hw).mpr hb, i, hi, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hle := ha.2 _ (Finset.mem_insert_of_mem ht)
    apply lt_of_le_of_ne hle
    intro heq
    exact hnot (π.injective heq ▸ ht)

theorem probability_newWindowEvent (owner : Fin d → Fin n)
    (hinj : Function.Injective owner) {t : Fin d} {k s : ℕ} (hs : s ∈ laterStarts t k) :
    probability (newWindowEvent owner t k s) = 1 / ((k + 1 : ℝ) * k) := by
  classical
  have hw := window_of_mem_later hs
  have hst := hw.1
  have htk := hw.2.1
  have hsk := hw.2.2
  have hspos : 0 < s := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hs).1
  have hk : 0 < k := by omega
  let i : Fin d := ⟨s - 1, by omega⟩
  have hi : i.val + 1 = s := by dsimp [i]; omega
  let W := (positions d k s).image owner
  have ht : owner t ∈ W := Finset.mem_image_of_mem owner (pivot_mem_positions hw)
  have hnot : owner i ∉ W := predecessor_not_mem owner hinj hi
  have hcard : W.card = k := by
    rw [Finset.card_image_of_injective _ hinj, positions_card hsk]
  have herase : (insert (owner i) W).erase (owner i) = W :=
    Finset.erase_insert hnot
  have hbig : (insert (owner i) W).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hnot, hcard]
  rw [newWindowEvent_eq owner hinj hw hi]
  have hcount := card_mul_first_two (insert (owner i) W)
    (Finset.mem_insert_self _ _) (show owner t ∈ (insert (owner i) W).erase (owner i) by
      rwa [herase])
  rw [herase, hbig, hcard] at hcount
  have hprob := probability_eq_inv_of_mul_card _ (Nat.mul_pos (by omega) hk) hcount
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hprob

theorem tailEvent_subset_cover (owner : Fin d → Fin n) (t : Fin d) {k : ℕ}
    (hk : 0 < k) :
    tailEvent owner t k ⊆ clearEvent owner t k (firstStart t k) ∪
      (laterStarts t k).biUnion (newWindowEvent owner t k) := by
  classical
  intro π hπ
  have hgap := (Finset.mem_filter.mp hπ).2
  rcases long_gap_cover (pivot_not_mem_revealedBy owner π t) hk hgap with hc | hnew
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
  · obtain ⟨s, hs, hc, hi⟩ := hnew
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hi⟩⟩))

/-- The tail estimate is uniform in the list length, pivot, and fixed injective owners. -/
theorem probability_size_ge_le (owner : Fin d → Fin n) (hinj : Function.Injective owner)
    (t : Fin d) {k : ℕ} (hk : 0 < k) :
    probability (tailEvent owner t k) ≤ 2 / (k + 1 : ℝ) := by
  classical
  by_cases hkd : k ≤ d
  · have hc := probability_mono (tailEvent_subset_cover owner t hk)
    have hu := probability_union_le (clearEvent owner t k (firstStart t k))
      ((laterStarts t k).biUnion (newWindowEvent owner t k))
    have hb := probability_biUnion_le (laterStarts t k) (newWindowEvent owner t k)
    have hf := probability_clearEvent owner hinj (first_window t hk hkd)
    have he : (∑ s ∈ laterStarts t k, probability (newWindowEvent owner t k s)) =
        (laterStarts t k).card / ((k + 1 : ℝ) * k) := by
      calc
        _ = ∑ _s ∈ laterStarts t k, (1 / ((k + 1 : ℝ) * k)) :=
          Finset.sum_congr rfl (fun s hs => probability_newWindowEvent owner hinj hs)
        _ = _ := by simp [div_eq_mul_inv]
    have hcard : ((laterStarts t k).card : ℝ) ≤ k - 1 := by
      have h := laterStarts_card_le t hk
      have hcast : ((laterStarts t k).card : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast h
      simpa only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] using hcast
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hden : (0 : ℝ) < (k + 1) * k := mul_pos (by positivity) hkR
    have hbound := div_le_div_of_nonneg_right hcard hden.le
    have hid : 1 / (k : ℝ) + (k - 1) / ((k + 1) * k) = 2 / (k + 1) := by
      field_simp
      ring
    rw [hf] at hu
    rw [he] at hb
    linarith
  · have he : tailEvent owner t k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      have h := (Finset.mem_filter.mp hπ).2
      have := size_le_length (revealedBy owner π t) t
      omega
    rw [he, probability_empty]
    positivity

end SmpMax.General.Gap

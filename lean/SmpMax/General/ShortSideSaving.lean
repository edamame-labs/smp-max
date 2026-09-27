import SmpMax.General.RefinedLogBound

/-!
# A uniform saving when at most one stable partner lies to the right

The existing first-window cover has at most one later start in this case.
Keeping the improved tails at three and four gives a fixed entropy saving.
-/

namespace SmpMax.General

open FiniteProbability

namespace Gap

variable {d n : ℕ}

theorem probability_size_ge_le_starts (owner : Fin d → Fin n)
    (hinj : Function.Injective owner) (t : Fin d) {k : ℕ}
    (hk : 0 < k) (hkd : k ≤ d) :
    probability (tailEvent owner t k) ≤
      1 / (k : ℝ) + (laterStarts t k).card / ((k + 1 : ℝ) * k) := by
  classical
  have hc := probability_mono (tailEvent_subset_cover owner t hk)
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
  rw [hf] at hu
  rw [he] at hb
  linarith

theorem laterStarts_card_le_one (t : Fin d) (hshort : d ≤ t.val + 2) (k : ℕ) :
    (laterStarts t k).card ≤ 1 := by
  simp only [laterStarts, Nat.card_Ioc, firstStart, lastStart]
  omega

theorem probability_size_ge_le_short (owner : Fin d → Fin n)
    (hinj : Function.Injective owner) (t : Fin d) (hshort : d ≤ t.val + 2)
    {k : ℕ} (hk : 0 < k) :
    probability (tailEvent owner t k) ≤ 1 / (k : ℝ) + 1 / ((k + 1 : ℝ) * k) := by
  classical
  by_cases hkd : k ≤ d
  · have h := probability_size_ge_le_starts owner hinj t hk hkd
    have hcard : ((laterStarts t k).card : ℝ) ≤ 1 := by
      exact_mod_cast laterStarts_card_le_one t hshort k
    have hden : 0 ≤ ((k : ℝ) + 1) * k := by positivity
    have hdiv := div_le_div_of_nonneg_right hcard hden
    linarith
  · have he : tailEvent owner t k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      have h := (Finset.mem_filter.mp hπ).2
      have := size_le_length (revealedBy owner π t) t
      omega
    rw [he, probability_empty]
    positivity

end Gap

noncomputable def shortSideSaving : ℝ := logIncrement 1 / 12 + logIncrement 2 / 10

theorem Gap.average_log_size_le_refined_sub_short {d n : ℕ}
    (owner : Fin d → Fin n) (hinj : Function.Injective owner) (t : Fin d)
    (hshort : d ≤ t.val + 2) {N : ℕ} (hN : 0 < N) :
    average (fun π => Real.log (Gap.size (Gap.revealedBy owner π t) t)) ≤
      refinedLogBound N - shortSideSaving := by
  classical
  have h3 := Gap.probability_size_ge_le_short owner hinj t hshort (k := 3) (by norm_num)
  have h4 := Gap.probability_size_ge_le_short owner hinj t hshort (k := 4) (by norm_num)
  norm_num at h3 h4
  have hterm (j : ℕ) :
      probability (Gap.tailEvent owner t (j + 2)) * logIncrement j ≤
        gapTerm j - (if j = 1 then logIncrement 1 / 12 else 0) -
          (if j = 2 then logIncrement 2 / 10 else 0) := by
    by_cases h1 : j = 1
    · subst j
      norm_num [gapTerm]
      have h := mul_le_mul_of_nonneg_right h3 (logIncrement_nonneg 1)
      linarith
    by_cases h2 : j = 2
    · subst j
      norm_num [gapTerm]
      have h := mul_le_mul_of_nonneg_right h4 (logIncrement_nonneg 2)
      linarith
    · rw [if_neg h1, if_neg h2, sub_zero, sub_zero]
      have h := Gap.probability_size_ge_le owner hinj t (k := j + 2) (by omega)
      have he : ((j + 2 : ℕ) : ℝ) + 1 = (j : ℝ) + 3 := by push_cast; ring
      rw [he] at h
      exact mul_le_mul_of_nonneg_right h (logIncrement_nonneg j)
  have hsum := Finset.sum_le_sum (s := Finset.range (d + 4)) (fun j _ => hterm j)
  have h1mem : 1 ∈ Finset.range (d + 4) := Finset.mem_range.mpr (by omega)
  have h2mem : 2 ∈ Finset.range (d + 4) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_ite_eq', h1mem, h2mem, if_true] at hsum
  have hexp := average_log_eq_tail_sum
    (fun π => Gap.size (Gap.revealedBy owner π t) t) (d + 4)
    (fun π => Gap.size_pos _ _) (fun π => (Gap.size_le_length _ _).trans (by omega))
  change average (fun π => Real.log (Gap.size (Gap.revealedBy owner π t) t)) =
    ∑ j ∈ Finset.range (d + 4), probability (Gap.tailEvent owner t (j + 2)) *
      logIncrement j at hexp
  rw [hexp]
  have hbound := partialLogBound_le_refinedLogBound (d + 4) hN
  change (∑ j ∈ Finset.range (d + 4), gapTerm j) ≤ refinedLogBound N at hbound
  unfold shortSideSaving
  linarith

end SmpMax.General

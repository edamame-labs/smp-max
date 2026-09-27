import SmpMax.General.FiniteProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Linearity of finite averages and justified sums of event contributions -/

namespace SmpMax.General.FiniteProbability

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]

omit [Nonempty Ω] [DecidableEq Ω] in
theorem average_add (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

omit [Nonempty Ω] [DecidableEq Ω] in
theorem average_sub (f g : Ω → ℝ) :
    average (fun ω => f ω - g ω) = average f - average g := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

omit [Nonempty Ω] in
theorem average_event (E : Finset Ω) (c : ℝ) :
    average (fun ω => if ω ∈ E then c else 0) = probability E * c := by
  classical
  unfold average probability
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- Summing event contributions is justified by a pointwise inequality.
The events may overlap when their contributions telescope. -/
theorem sum_probability_mul_le_average {ι : Type*} (S : Finset ι)
    (E : ι → Finset Ω) (w : ι → ℝ) (f : Ω → ℝ)
    (h : ∀ ω, (∑ i ∈ S, if ω ∈ E i then w i else 0) ≤ f ω) :
    (∑ i ∈ S, probability (E i) * w i) ≤ average f := by
  have hh := average_mono h
  rw [average_finset_sum] at hh
  simpa only [average_event] using hh

omit [Fintype Ω] [Nonempty Ω] in
theorem disjoint_events_pointwise {ι : Type*} (S : Finset ι)
    (E : ι → Finset Ω) (w : ι → ℝ) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hE : ∀ i ∈ S, ∀ ω ∈ E i, w i ≤ f ω)
    (hd : ∀ i ∈ S, ∀ j ∈ S, ∀ ω, ω ∈ E i → ω ∈ E j → i = j) (ω : Ω) :
    (∑ i ∈ S, if ω ∈ E i then w i else 0) ≤ f ω := by
  classical
  by_cases hex : ∃ i ∈ S, ω ∈ E i
  · obtain ⟨i, hi, hω⟩ := hex
    rw [Finset.sum_eq_single i]
    · simpa only [if_pos hω] using hE i hi ω hω
    · intro j hj hji
      rw [if_neg (fun h => hji (hd j hj i hi ω h hω))]
    · exact fun hn => (hn hi).elim
  · have hn : ∀ i ∈ S, ω ∉ E i := by simpa using hex
    simpa only [Finset.sum_congr rfl (fun i hi => if_neg (hn i hi)), Finset.sum_const_zero]
      using hf ω

omit [DecidableEq Ω] in
theorem disjoint_events_average {ι : Type*} (S : Finset ι)
    (E : ι → Finset Ω) (w : ι → ℝ) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hE : ∀ i ∈ S, ∀ ω ∈ E i, w i ≤ f ω)
    (hd : ∀ i ∈ S, ∀ j ∈ S, ∀ ω, ω ∈ E i → ω ∈ E j → i = j) :
    (∑ i ∈ S, probability (E i) * w i) ≤ average f := by
  classical
  exact sum_probability_mul_le_average S E w f (disjoint_events_pointwise S E w f hf hE hd)

end SmpMax.General.FiniteProbability

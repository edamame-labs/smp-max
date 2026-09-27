import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Uniform probability on a nonempty finite space

All probabilities are normalized cardinalities. No measure-theoretic
independence or distributional assumptions enter the permutation argument.
-/

namespace SmpMax.General.FiniteProbability

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def probability (E : Finset Ω) : ℝ := E.card / Fintype.card Ω

noncomputable def average (f : Ω → ℝ) : ℝ := (∑ x, f x) / Fintype.card Ω

theorem total_pos : (0 : ℝ) < Fintype.card Ω := by
  exact_mod_cast Fintype.card_pos

theorem probability_nonneg (E : Finset Ω) : 0 ≤ probability E := by
  unfold probability
  positivity

theorem probability_mono {E F : Finset Ω} (h : E ⊆ F) :
    probability E ≤ probability F := by
  apply div_le_div_of_nonneg_right _ (le_of_lt (total_pos (Ω := Ω)))
  exact_mod_cast Finset.card_le_card h

omit [Nonempty Ω] in
theorem probability_empty : probability (∅ : Finset Ω) = 0 := by
  simp [probability]

theorem probability_union_le [DecidableEq Ω] (E F : Finset Ω) :
    probability (E ∪ F) ≤ probability E + probability F := by
  classical
  unfold probability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt (total_pos (Ω := Ω)))
  exact_mod_cast Finset.card_union_le E F

theorem probability_biUnion_le [DecidableEq Ω] {ι : Type*} (S : Finset ι) (E : ι → Finset Ω) :
    probability (S.biUnion E) ≤ ∑ i ∈ S, probability (E i) := by
  classical
  unfold probability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt (total_pos (Ω := Ω)))
  exact_mod_cast Finset.card_biUnion_le

/-- An exact cardinality identity certifies a reciprocal probability. -/
theorem probability_eq_inv_of_mul_card (E : Finset Ω) {m : ℕ} (hm : 0 < m)
    (h : m * E.card = Fintype.card Ω) : probability E = 1 / (m : ℝ) := by
  unfold probability
  apply (div_eq_div_iff (ne_of_gt (total_pos (Ω := Ω))) (by positivity)).mpr
  simp only [one_mul]
  have hc : (m : ℝ) * E.card = Fintype.card Ω := by exact_mod_cast h
  simpa only [mul_comm] using hc

theorem average_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x))
    (le_of_lt (total_pos (Ω := Ω)))

theorem average_const (c : ℝ) : average (fun _ : Ω => c) = c := by
  simp [average, ne_of_gt (total_pos (Ω := Ω))]

omit [Nonempty Ω] in
theorem average_finset_sum {ι : Type*} (S : Finset ι) (f : ι → Ω → ℝ) :
    average (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

end SmpMax.General.FiniteProbability

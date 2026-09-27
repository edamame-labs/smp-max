import SmpMax.General.FiniteProbability
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# At most two exceptions can charge the same successor owner

This finite-map lemma supplies the global accounting step in the structural
entropy argument. It is separate from the matching interpretation and the
relative-order probability estimates.
-/

namespace SmpMax.General.SuccessorCharging

variable {α : Type*} [Fintype α] [DecidableEq α]

def Exceptional (g b : α → α) (m : α) : Prop :=
  g (g m) = m ∧ b m ≠ m ∧ b m ≠ g m ∧ (g (b m) = m ∨ g (b m) = g m)

omit [Fintype α] [DecidableEq α] in
theorem exception_charges_noncycle {g b : α → α} {m : α}
    (h : Exceptional g b m) : g (g (b m)) ≠ b m := by
  rcases h with ⟨hcycle, hbm, hba, hreturn | hreturn⟩
  · rw [hreturn]
    exact hba.symm
  · rw [hreturn, hcycle]
    exact hbm.symm

omit [Fintype α] in
theorem exception_in_pair {g b : α → α} {m u : α}
    (h : Exceptional g b m) (hcharge : b m = u) : m ∈ ({g u, g (g u)} : Finset α) := by
  rcases h.2.2.2 with hreturn | hreturn
  · have he : m = g u := by rw [← hcharge, hreturn]
    simp [he]
  · have he : m = g (g u) := by rw [← hcharge, hreturn, h.1]
    simp [he]

/-- Exceptional vertices map into non-two-cycles, with fibers of size at most two. -/
theorem card_exceptions_le_twice_noncycles (g b : α → α) (D : Finset α)
    (hD : ∀ m ∈ D, Exceptional g b m) :
    D.card ≤ 2 * (Finset.univ.filter (fun u => g (g u) ≠ u)).card := by
  classical
  let B := Finset.univ.filter (fun u => g (g u) ≠ u)
  have hmap : ∀ m ∈ D, b m ∈ B := by
    intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, exception_charges_noncycle (hD m hm)⟩
  have hfiber (u : α) : (D.filter (fun m => b m = u)).card ≤ 2 := by
    have hsub : D.filter (fun m => b m = u) ⊆ {g u, g (g u)} := by
      intro m hm
      have hp := Finset.mem_filter.mp hm
      exact exception_in_pair (hD m hp.1) hp.2
    have hp : ({g u, g (g u)} : Finset α).card ≤ 2 := by
      simpa using Finset.card_insert_le (g u) ({g (g u)} : Finset α)
    exact (Finset.card_le_card hsub).trans hp
  calc
    D.card = ∑ u ∈ B, (D.filter (fun m => b m = u)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _u ∈ B, 2 := Finset.sum_le_sum (fun u _ => hfiber u)
    _ = 2 * B.card := by simp [Nat.mul_comm]

omit [DecidableEq α] in
/-- Local savings of three units on non-two-cycles pay for every exception. -/
theorem sum_saving_ge (g b : α → α) (D : Finset α)
    (hD : ∀ m ∈ D, Exceptional g b m) (s : α → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hzero : ∀ m, 0 ≤ s m)
    (hbase : ∀ m, m ∉ D → δ ≤ s m)
    (hbad : ∀ m, g (g m) ≠ m → 3 * δ ≤ s m) :
    (Fintype.card α : ℝ) * δ ≤ ∑ m, s m := by
  classical
  let B := Finset.univ.filter (fun m => g (g m) ≠ m)
  have hpoint (m : α) :
      δ + (if m ∈ B then 2 * δ else 0) ≤ s m + (if m ∈ D then δ else 0) := by
    by_cases hb : m ∈ B
    · have hs := hbad m (Finset.mem_filter.mp hb).2
      rw [if_pos hb]
      by_cases hd : m ∈ D <;> simp only [hd, if_true, if_false] <;> linarith
    · rw [if_neg hb]
      by_cases hd : m ∈ D
      · rw [if_pos hd]
        linarith [hzero m]
      · rw [if_neg hd]
        simpa using hbase m hd
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun m _ => hpoint m)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hind (E : Finset α) (c : ℝ) :
      (∑ m : α, if m ∈ E then c else 0) = (E.card : ℝ) * c := by
    rw [← Finset.sum_filter]
    simp
  rw [hind B, hind D] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hc : (D.card : ℝ) ≤ 2 * B.card := by
    exact_mod_cast card_exceptions_le_twice_noncycles g b D hD
  have hpay := mul_le_mul_of_nonneg_right hc hδ
  nlinarith

end SmpMax.General.SuccessorCharging

import SmpMax.General.PermutationRevelation
import Mathlib.Data.Finset.Sort

/-!
# Revelation with ranks in a larger finite set

Only real men are matching coordinates. Auxiliary labels can be used to
sample ranks, since the counting inequality holds for every injective rank
assignment. No uniform restriction theorem is needed.
-/

namespace SmpMax.General

open FiniteProbability

variable {n N : ℕ}

def earlierByRank (rank : Fin n → Fin N) (m : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => rank u < rank m)

theorem supportCost_eq_injective_rank_sum_aux (I : Profile n) (μ : Matching n)
    (π : Fin n → Fin N) (order : List (Fin n)) (R : Finset (Fin n))
    (hp : order.Pairwise (fun a b => π a < π b))
    (hc : ∀ u, u ∈ R ∨ u ∈ order)
    (hR : ∀ u ∈ R, ∀ v ∈ order, π u < π v) :
    supportCost I μ R order =
      (order.map (fun m =>
        Real.log (partnerSupportFinset I μ (earlierByRank π m) m).card)).sum := by
  induction order generalizing R with
  | nil => rfl
  | cons m rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hp
    have heq : R = earlierByRank π m := by
      ext u
      constructor
      · intro hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR u hu m List.mem_cons_self⟩
      · intro hu
        have hlt := (Finset.mem_filter.mp hu).2
        rcases hc u with huR | huL
        · exact huR
        · rcases List.mem_cons.mp huL with rfl | huL
          · exact (lt_irrefl _ hlt).elim
          · exact (not_lt_of_ge (hhead u huL).le hlt).elim
    have hc' : ∀ u, u ∈ insert m R ∨ u ∈ rest := by
      intro u
      rcases hc u with hu | hu
      · exact Or.inl (Finset.mem_insert_of_mem hu)
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl (Finset.mem_insert_self _ _)
        · exact Or.inr hu
    have hR' : ∀ u ∈ insert m R, ∀ v ∈ rest, π u < π v := by
      intro u hu v hv
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hhead v hv
      · exact hR u hu v (List.mem_cons_of_mem _ hv)
    rw [supportCost, List.map_cons, List.sum_cons, ih _ hrest hc' hR', heq]


theorem exists_injective_rank_order (rank : Fin n → Fin N)
    (hinj : Function.Injective rank) :
    ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      order.Pairwise (fun a b => rank a < rank b) := by
  classical
  let r : Fin n → Fin n → Prop := fun a b => rank a ≤ rank b
  let : IsTrans (Fin n) r := ⟨fun _ _ _ => le_trans⟩
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => hinj (le_antisymm h₁ h₂)⟩
  let : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let order := (Finset.univ : Finset (Fin n)).sort r
  have hn : order.Nodup := Finset.sort_nodup _ _
  have hp : order.Pairwise (fun a b => rank a < rank b) := by
    have hle : order.Pairwise r := Finset.pairwise_sort _ _
    exact (hle.and hn).imp (fun {a b} h =>
      lt_of_le_of_ne h.1 (fun he => h.2 (hinj he)))
  refine ⟨order, ?_, hp⟩
  apply List.perm_ext_iff_of_nodup hn (List.nodup_finRange n) |>.mpr
  intro a
  simp [order]

/-- Fixed-rank entropy counting, including ranks sampled with auxiliary labels. -/
theorem stableCount_mul_log_le_sum_rank_support (I : Profile n)
    (rank : Fin n → Fin N) (hinj : Function.Injective rank) :
    (stableCount I : ℝ) * Real.log (stableCount I) ≤
      ∑ μ ∈ stableMatchings I, ∑ m,
        Real.log (partnerSupportFinset I μ (earlierByRank rank m) m).card := by
  obtain ⟨order, hperm, hpair⟩ := exists_injective_rank_order rank hinj
  have hcov : ∀ m, m ∈ order := fun m => hperm.mem_iff.mpr (List.mem_finRange m)
  have heq (μ : Matching n) : supportCost I μ ∅ order =
      ∑ m, Real.log (partnerSupportFinset I μ (earlierByRank rank m) m).card := by
    rw [supportCost_eq_injective_rank_sum_aux I μ rank order ∅ hpair
      (fun m => Or.inr (hcov m)) (by simp)]
    rw [(hperm.map _).sum_eq, ← List.ofFn_eq_map, List.sum_ofFn]
  simpa only [heq] using stableCount_mul_log_le_sum_supportCost I order hcov

/-- Aggregate savings may depend on the reference matching and coordinate. -/
theorem stableCount_le_exp_of_average_rank_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (I : Profile n) (rank : Ω → Fin n → Fin N)
    (hinj : ∀ ω, Function.Injective (rank ω)) (C : ℝ)
    (hC : ∀ μ : Matching n, Stable I μ →
      average (fun ω => ∑ m,
        Real.log (partnerSupportFinset I μ (earlierByRank (rank ω) m) m).card) ≤ n * C) :
    (stableCount I : ℝ) ≤ Real.exp (n * C) := by
  classical
  have h := average_mono (fun ω => stableCount_mul_log_le_sum_rank_support I (rank ω) (hinj ω))
  rw [average_const, average_finset_sum] at h
  have hb : (∑ μ ∈ stableMatchings I, average (fun ω => ∑ m,
      Real.log (partnerSupportFinset I μ (earlierByRank (rank ω) m) m).card)) ≤
      (stableCount I : ℝ) * (n * C) := by
    calc
      _ ≤ ∑ _μ ∈ stableMatchings I, (n : ℝ) * C :=
        Finset.sum_le_sum (fun μ hμ => hC μ (Finset.mem_filter.mp hμ).2)
      _ = _ := by simp [stableCount]
  have hall := h.trans hb
  by_cases hz : stableCount I = 0
  · simp only [hz, Nat.cast_zero]
    exact (Real.exp_pos _).le
  · have hp : (0 : ℝ) < stableCount I := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (Real.log_le_iff_le_exp hp).mp (le_of_mul_le_mul_left hall hp)

end SmpMax.General

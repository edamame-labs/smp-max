import SmpMax.General.Definitions
import SmpMax.General.FiniteRevelation

/-!
# The finite revelation inequality for stable matchings

The coordinate list contains fixed men. Every conditional family agrees
with the reference matching on the entire revealed set. No random order
or probability estimate is assumed or proved in this file.
-/

namespace SmpMax.General

variable {n : ℕ}

/-- All stable matchings agreeing with the reference on every revealed coordinate. -/
noncomputable def compatibleFamily (I : Profile n) (μ : Matching n)
    (revealed : Finset (Fin n)) : Finset (Matching n) := by
  classical
  exact Finset.univ.filter (Compatible I μ revealed)

theorem compatibleFamily_empty (I : Profile n) (μ : Matching n) :
    compatibleFamily I μ ∅ = stableMatchings I := by
  classical
  ext ν
  simp [compatibleFamily, stableMatchings, Compatible, AgreesOn]

/-- Coordinate images of full compatible families are exactly the defined support. -/
theorem compatibleFamily_image (I : Profile n) (μ : Matching n)
    (revealed : Finset (Fin n)) (m : Fin n) :
    (compatibleFamily I μ revealed).image (fun ν => ν m) =
      partnerSupportFinset I μ revealed m := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ν, (Finset.mem_filter.mp hν).2, rfl⟩
  · intro hw
    obtain ⟨ν, hν, hνm⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_image.mpr ⟨ν,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hν⟩, hνm⟩

/-- Conditioning on one more coordinate adds that man to the revealed set. -/
theorem compatibleFamily_fiber (I : Profile n) (μ : Matching n)
    (revealed : Finset (Fin n)) (m : Fin n) :
    Revelation.fiber (compatibleFamily I μ revealed) (fun ν => ν m) (μ m) =
      compatibleFamily I μ (insert m revealed) := by
  classical
  ext ν
  simp only [Revelation.fiber, compatibleFamily, Finset.mem_filter,
    Finset.mem_univ, true_and, Compatible, AgreesOn, Finset.mem_insert,
    forall_eq_or_imp]
  tauto

/-- Sum of log exact support sizes while revealing fixed men in the given order. -/
noncomputable def supportCost (I : Profile n) (μ : Matching n) :
    Finset (Fin n) → List (Fin n) → ℝ
  | _, [] => 0
  | revealed, m :: rest => Real.log (partnerSupportFinset I μ revealed m).card +
      supportCost I μ (insert m revealed) rest

/-- The recursive finite-family cost coincides with the full-prefix partner cost. -/
theorem cost_eq_supportCost (I : Profile n) (μ : Matching n)
    (order : List (Fin n)) (revealed : Finset (Fin n)) :
    Revelation.cost (order.map (fun m => fun ν : Matching n => ν m))
      (compatibleFamily I μ revealed) μ = supportCost I μ revealed order := by
  induction order generalizing revealed with
  | nil => rfl
  | cons m rest ih =>
    simp only [List.map_cons, Revelation.cost, supportCost,
      compatibleFamily_image, compatibleFamily_fiber, ih]

/-- A fixed list revealing every man distinguishes the matching outcomes. -/
theorem matching_coordinates_separate (order : List (Fin n))
    (hcovers : ∀ m, m ∈ order) (s : Finset (Matching n)) :
    Revelation.Separates (order.map (fun m => fun ν : Matching n => ν m)) s := by
  intro μ _ ν _ h
  apply Equiv.ext
  intro m
  exact h _ (List.mem_map_of_mem (hcovers m))

/-- The matching count is bounded by full-prefix support costs for every fixed order. -/
theorem stableCount_mul_log_le_sum_supportCost (I : Profile n) (order : List (Fin n))
    (hcovers : ∀ m, m ∈ order) :
    (stableCount I : ℝ) * Real.log (stableCount I) ≤
      ∑ μ ∈ stableMatchings I, supportCost I μ ∅ order := by
  classical
  have h := Revelation.count_le_sum_cost _ (stableMatchings I)
    (matching_coordinates_separate order hcovers _)
  change ((stableMatchings I).card : ℝ) * Real.log (stableMatchings I).card ≤ _
  calc
    _ ≤ _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _
      rw [← compatibleFamily_empty I μ, cost_eq_supportCost]

end SmpMax.General

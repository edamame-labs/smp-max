import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Filter

/-!
# Complete strict stable marriage at arbitrary order

Men and women are separately interpreted copies of `Fin n`. A rank row
is a permutation, with smaller values preferred. A matching maps men
bijectively to women. No rotation-size or dominance assumption is built
into these definitions.
-/

namespace SmpMax.General

/-- Complete strict preference lists, represented by their rank functions. -/
structure Profile (n : ℕ) where
  men : Fin n → Equiv.Perm (Fin n)
  women : Fin n → Equiv.Perm (Fin n)

/-- A perfect matching, with its inverse partner map available explicitly. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

variable {n : ℕ}

/-- A pair blocks a matching exactly when both participants prefer each other. -/
def Blocks (I : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  I.men m w < I.men m (μ m) ∧ I.women w m < I.women w (μ.symm w)

/-- Stability has no auxiliary structural hypotheses. -/
def Stable (I : Profile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ Blocks I μ m w

/-- A stable pair occurs in at least one stable matching of this profile. -/
def StablePair (I : Profile n) (m w : Fin n) : Prop :=
  ∃ μ : Matching n, Stable I μ ∧ μ m = w

/-- Agreement on the complete set of revealed men's coordinates. -/
def AgreesOn (μ ν : Matching n) (revealed : Finset (Fin n)) : Prop :=
  ∀ u ∈ revealed, ν u = μ u

/-- The full family of stable matchings consistent with a revealed prefix. -/
def Compatible (I : Profile n) (μ : Matching n) (revealed : Finset (Fin n))
    (ν : Matching n) : Prop :=
  Stable I ν ∧ AgreesOn μ ν revealed

/-- Exact possible partners after all the specified coordinates are fixed. -/
def PartnerSupport (I : Profile n) (μ : Matching n) (revealed : Finset (Fin n))
    (m : Fin n) : Set (Fin n) :=
  {w | ∃ ν : Matching n, Compatible I μ revealed ν ∧ ν m = w}

/-- The same exact support as a finite set, for its cardinality. -/
noncomputable def partnerSupportFinset (I : Profile n) (μ : Matching n)
    (revealed : Finset (Fin n)) (m : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => w ∈ PartnerSupport I μ revealed m)

/-- All stable matchings of the profile. -/
noncomputable def stableMatchings (I : Profile n) : Finset (Matching n) := by
  classical
  exact Finset.univ.filter (Stable I)

/-- The number of all stable matchings of the profile. -/
noncomputable def stableCount (I : Profile n) : ℕ :=
  (stableMatchings I).card

theorem stable_iff_no_block (I : Profile n) (μ : Matching n) :
    Stable I μ ↔ ∀ m w,
      ¬ (I.men m w < I.men m (μ m) ∧ I.women w m < I.women w (μ.symm w)) :=
  Iff.rfl

theorem Stable.stablePair {I : Profile n} {μ : Matching n} (hμ : Stable I μ)
    (m : Fin n) : StablePair I m (μ m) :=
  ⟨μ, hμ, rfl⟩

theorem Stable.mem_partnerSupport {I : Profile n} {μ : Matching n}
    (hμ : Stable I μ) (revealed : Finset (Fin n)) (m : Fin n) :
    μ m ∈ PartnerSupport I μ revealed m :=
  ⟨μ, ⟨hμ, fun _ _ => rfl⟩, rfl⟩

theorem mem_partnerSupport_stablePair {I : Profile n} {μ : Matching n}
    {revealed : Finset (Fin n)} {m w : Fin n}
    (hw : w ∈ PartnerSupport I μ revealed m) : StablePair I m w := by
  obtain ⟨ν, hν, rfl⟩ := hw
  exact hν.1.stablePair m

end SmpMax.General

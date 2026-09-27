import SmpMax.General.Definitions
import Mathlib.Data.Set.Finite.Basic

/-!
# Stable-pair separation for arbitrary order

This is a formal proof of the classical decomposition/opposition lemma,
not a claim of a new structural theorem. See Roth, Rothblum and Vande
Vate (1993), Lemma 11, which credits Knuth (1976).

The proof uses a finite invariant set instead of explicitly traversing
alternating cycles. It assumes neither global male dominance nor a
restriction on rotation sizes.
-/

namespace SmpMax.General

variable {n : ℕ} {I : Profile n} {μ ν : Matching n}

theorem Stable.woman_prefers_of_man_prefers (hμ : Stable I μ) {m w : Fin n}
    (hm : I.men m w < I.men m (μ m)) :
    I.women w (μ.symm w) < I.women w m := by
  have hle : I.women w (μ.symm w) ≤ I.women w m :=
    le_of_not_gt (fun hw => hμ m w ⟨hm, hw⟩)
  have hne : I.women w (μ.symm w) ≠ I.women w m := by
    intro heq
    have heq' := (I.women w).injective heq
    have hw : w = μ m := by simpa using congrArg μ heq'
    exact (ne_of_lt hm) (congrArg (I.men m) hw)
  exact lt_of_le_of_ne hle hne

theorem Stable.man_prefers_of_woman_prefers (hμ : Stable I μ) {m w : Fin n}
    (hw : I.women w m < I.women w (μ.symm w)) :
    I.men m (μ m) < I.men m w := by
  have hle : I.men m (μ m) ≤ I.men m w :=
    le_of_not_gt (fun hm => hμ m w ⟨hm, hw⟩)
  have hne : I.men m (μ m) ≠ I.men m w := by
    intro heq
    have heq' := (I.men m).injective heq
    have hm : m = μ.symm w := by simpa using congrArg μ.symm heq'
    exact (ne_of_lt hw) (congrArg (I.women w) hm)
  exact lt_of_le_of_ne hle hne

/-- Men preferring `μ` to `ν` form an invariant set under `ν⁻¹ ∘ μ`. -/
theorem prefers_first_closed (hμ : Stable I μ) (hν : Stable I ν)
    {m : Fin n} (hm : I.men m (μ m) < I.men m (ν m)) :
    I.men (ν.symm (μ m)) (μ (ν.symm (μ m))) <
      I.men (ν.symm (μ m)) (ν (ν.symm (μ m))) := by
  have hw := hν.woman_prefers_of_man_prefers hm
  have hm' := hμ.man_prefers_of_woman_prefers (m := ν.symm (μ m)) (w := μ m) (by
    simpa only [Equiv.symm_apply_apply] using hw)
  simpa only [Equiv.apply_symm_apply] using hm'

/-- On an edge of either stable matching, the two sides have opposite interests. -/
theorem stable_opposition (hμ : Stable I μ) (hν : Stable I ν) (m : Fin n) :
    I.men m (ν m) < I.men m (μ m) ↔
      I.women (ν m) (μ.symm (ν m)) < I.women (ν m) m := by
  constructor
  · exact hμ.woman_prefers_of_man_prefers
  · intro hw
    let A : Set (Fin n) := {u | I.men u (μ u) < I.men u (ν u)}
    let f : Fin n → Fin n := fun u => ν.symm (μ u)
    have hf : Function.Injective f := ν.symm.injective.comp μ.injective
    have hmap : Set.MapsTo f A A := fun u hu => prefers_first_closed hμ hν hu
    have hsurj : Set.SurjOn f A A :=
      ((Set.toFinite A).injOn_iff_bijOn_of_mapsTo hmap).mp hf.injOn |>.surjOn
    by_contra hn
    have hne : ν m ≠ μ m := by
      intro heq
      have : μ.symm (ν m) = m := by rw [heq, Equiv.symm_apply_apply]
      rw [this] at hw
      exact (lt_irrefl _) hw
    have hmA : m ∈ A := lt_of_le_of_ne (le_of_not_gt hn) (by
      intro heq
      exact hne ((I.men m).injective heq).symm)
    obtain ⟨u, huA, hum⟩ := hsurj hmA
    have hμu : μ u = ν m := by
      simpa only [f, Equiv.apply_symm_apply] using congrArg ν hum
    have hu : u = μ.symm (ν m) := by
      simpa only [Equiv.symm_apply_apply] using congrArg μ.symm hμu
    have hw' := hν.woman_prefers_of_man_prefers huA
    rw [hμu, Equiv.symm_apply_apply, hu] at hw'
    exact (lt_asymm hw hw')

/-- A stable pair separates the partners in any other stable matching.
The equivalence also covers the matched case, when both inequalities are false. -/
theorem stable_pair_separation {m w : Fin n} (hp : StablePair I m w)
    (hμ : Stable I μ) :
    I.men m w < I.men m (μ m) ↔ I.women w (μ.symm w) < I.women w m := by
  obtain ⟨ν, hν, rfl⟩ := hp
  exact stable_opposition hμ hν m

end SmpMax.General

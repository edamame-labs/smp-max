import SmpMax.General.Separation

/-!
# Revealed stable pairs are barriers

The revealed coordinates are men, fixed independently of the matching.
Agreement on a man's partner also fixes that woman's inverse partner.
Separation then places every compatible partner on the same side of
each revealed stable partner as the reference outcome.
-/

namespace SmpMax.General

variable {n : ℕ} {I : Profile n} {μ ν : Matching n}
  {revealed : Finset (Fin n)} {m w : Fin n}

/-- A revealed man's coordinate fixes the inverse coordinate of his partner. -/
theorem AgreesOn.inverse_eq (h : AgreesOn μ ν revealed)
    (hw : μ.symm w ∈ revealed) : ν.symm w = μ.symm w := by
  have hp := h (μ.symm w) hw
  have hp' : ν (μ.symm w) = w := by simpa only [Equiv.apply_symm_apply] using hp
  simpa only [Equiv.symm_apply_apply] using (congrArg ν.symm hp').symm

/-- A revealed woman belongs to the same side of every compatible partner.
This uses all revealed coordinates, not only their number. -/
theorem compatible_same_side (hp : StablePair I m w) (hμ : Stable I μ)
    (hν : Compatible I μ revealed ν) (hw : μ.symm w ∈ revealed) :
    (I.men m w < I.men m (ν m)) ↔ (I.men m w < I.men m (μ m)) := by
  rw [stable_pair_separation hp hν.1, stable_pair_separation hp hμ,
    hν.2.inverse_eq hw]

theorem compatible_avoids_revealed (hν : Compatible I μ revealed ν)
    (hw : μ.symm w ∈ revealed) (hne : w ≠ μ m) : ν m ≠ w := by
  intro heq
  have hi := hν.2.inverse_eq hw
  have hi' : ν.symm w = m := by rw [← heq, Equiv.symm_apply_apply]
  rw [hi'] at hi
  have : μ m = w := by simpa only [Equiv.apply_symm_apply] using congrArg μ hi
  exact hne this.symm

/-- A barrier preferred to the reference partner is preferred to every candidate. -/
theorem compatible_lower_barrier (hp : StablePair I m w) (hμ : Stable I μ)
    (hν : Compatible I μ revealed ν) (hw : μ.symm w ∈ revealed)
    (hlt : I.men m w < I.men m (μ m)) : I.men m w < I.men m (ν m) :=
  (compatible_same_side hp hμ hν hw).mpr hlt

/-- Every candidate is preferred to a barrier below the reference partner. -/
theorem compatible_upper_barrier (hp : StablePair I m w) (hμ : Stable I μ)
    (hν : Compatible I μ revealed ν) (hw : μ.symm w ∈ revealed)
    (hlt : I.men m (μ m) < I.men m w) : I.men m (ν m) < I.men m w := by
  have hnot : ¬ I.men m w < I.men m (ν m) := by
    intro h
    exact lt_asymm hlt ((compatible_same_side hp hμ hν hw).mp h)
  have hne : ν m ≠ w := compatible_avoids_revealed hν hw (by
    intro h
    rw [h] at hlt
    exact (lt_irrefl _) hlt)
  exact lt_of_le_of_ne (le_of_not_gt hnot) (fun h => hne ((I.men m).injective h))

/-- Pointwise support inclusion for any revealed lower and upper barriers. -/
theorem partnerSupport_between {lower upper : Fin n}
    (hl : StablePair I m lower) (hu : StablePair I m upper) (hμ : Stable I μ)
    (hrl : μ.symm lower ∈ revealed) (hru : μ.symm upper ∈ revealed)
    (hlt : I.men m lower < I.men m (μ m))
    (hut : I.men m (μ m) < I.men m upper) :
    PartnerSupport I μ revealed m ⊆
      {w | I.men m lower < I.men m w ∧ I.men m w < I.men m upper} := by
  rintro w ⟨ν, hν, rfl⟩
  exact ⟨compatible_lower_barrier hl hμ hν hrl hlt,
    compatible_upper_barrier hu hμ hν hru hut⟩

end SmpMax.General

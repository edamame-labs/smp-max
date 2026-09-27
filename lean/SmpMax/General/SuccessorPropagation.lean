import SmpMax.General.PartnerIntervals

/-!
# Changes forced through the next worse stable partner

Crossing a stable partner forces her reference owner to become worse off.
This implication can be iterated. It supplies exclusions beyond the
single-list revelation gap without a rotation-poset representation.
-/

namespace SmpMax.General

variable {n : ℕ} {I : Profile n} {μ ν : Matching n}

theorem stable_pair_woman_prefers_of_worse {m w : Fin n}
    (hp : StablePair I m w) (hμ : Stable I μ)
    (hw : I.men m (μ m) < I.men m w) :
    I.women w m < I.women w (μ.symm w) := by
  have hn : ¬ I.women w (μ.symm w) < I.women w m := by
    intro h
    exact lt_asymm hw ((stable_pair_separation hp hμ).mpr h)
  apply lt_of_le_of_ne (le_of_not_gt hn)
  intro h
  have he := (I.women w).injective h
  have hew : μ m = w := by simpa using congrArg μ he
  rw [hew] at hw
  exact (lt_irrefl _) hw

/-- Moving to or beyond a worse stable partner makes her old owner worse off. -/
theorem crossing_forces_owner_worse {m w : Fin n}
    (hp : StablePair I m w) (hμ : Stable I μ) (hν : Stable I ν)
    (hbefore : I.men m (μ m) < I.men m w)
    (hcross : I.men m w ≤ I.men m (ν m)) :
    I.men (μ.symm w) (μ (μ.symm w)) < I.men (μ.symm w) (ν (μ.symm w)) := by
  have hwm := stable_pair_woman_prefers_of_worse hp hμ hbefore
  have hnew : I.women w (ν.symm w) ≤ I.women w m := by
    rcases lt_or_eq_of_le hcross with hlt | heq
    · exact (hν.woman_prefers_of_man_prefers hlt).le
    · have he := (I.men m).injective heq
      rw [he, Equiv.symm_apply_apply]
  have howner := (stable_pair_separation (hμ.stablePair (μ.symm w)) hν).mpr
    (by simpa only [Equiv.apply_symm_apply] using hnew.trans_lt hwm)
  exact howner

noncomputable def worsePartners (I : Profile n) (μ : Matching n) (m : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => StablePair I m w ∧ I.men m (μ m) < I.men m w)

noncomputable def nextWorsePartner (I : Profile n) (μ : Matching n) (m : Fin n) :
    Fin n := by
  classical
  exact if h : (worsePartners I μ m).Nonempty then
    Classical.choose ((worsePartners I μ m).exists_min_image (I.men m) h)
  else μ m

noncomputable def successorOwner (I : Profile n) (μ : Matching n) (m : Fin n) :
    Fin n := μ.symm (nextWorsePartner I μ m)

theorem nextWorsePartner_spec {m : Fin n} (h : (worsePartners I μ m).Nonempty) :
    StablePair I m (nextWorsePartner I μ m) ∧
    I.men m (μ m) < I.men m (nextWorsePartner I μ m) ∧
    ∀ w ∈ worsePartners I μ m, I.men m (nextWorsePartner I μ m) ≤ I.men m w := by
  classical
  simp only [nextWorsePartner, dif_pos h]
  have hs := Classical.choose_spec ((worsePartners I μ m).exists_min_image (I.men m) h)
  exact ⟨(Finset.mem_filter.mp hs.1).2.1, (Finset.mem_filter.mp hs.1).2.2, hs.2⟩

theorem successorOwner_ne_of_worse {m : Fin n}
    (h : (worsePartners I μ m).Nonempty) : successorOwner I μ m ≠ m := by
  intro he
  have hew : nextWorsePartner I μ m = μ m := by
    simpa only [successorOwner, Equiv.apply_symm_apply] using congrArg μ he
  have hs := (nextWorsePartner_spec h).2.1
  rw [hew] at hs
  exact (lt_irrefl _) hs

/-- Every worsening in a stable outcome propagates along the fixed successor map. -/
theorem worsening_propagates (hμ : Stable I μ) (hν : Stable I ν) {m : Fin n}
    (hm : I.men m (μ m) < I.men m (ν m)) :
    I.men (successorOwner I μ m) (μ (successorOwner I μ m)) <
      I.men (successorOwner I μ m) (ν (successorOwner I μ m)) := by
  classical
  have hmem : ν m ∈ worsePartners I μ m :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hν.stablePair m, hm⟩
  have hs := nextWorsePartner_spec ⟨ν m, hmem⟩
  exact crossing_forces_owner_worse hs.1 hμ hν hs.2.1 (hs.2.2 _ hmem)

/-- A revealed successor of a candidate's owner excludes that candidate and all worse ones. -/
theorem compatible_successor_upper_barrier {m w : Fin n} {R : Finset (Fin n)}
    (hp : StablePair I m w) (hμ : Stable I μ) (hν : Compatible I μ R ν)
    (hbefore : I.men m (μ m) < I.men m w)
    (hseen : successorOwner I μ (μ.symm w) ∈ R) :
    I.men m (ν m) < I.men m w := by
  by_contra hn
  have h1 := crossing_forces_owner_worse hp hμ hν.1 hbefore (le_of_not_gt hn)
  have h2 := worsening_propagates hμ hν.1 h1
  rw [hν.2 _ hseen] at h2
  exact (lt_irrefl _) h2

end SmpMax.General

import SmpMax.General.SuccessorPropagation

/-!
# Changes toward better stable partners also propagate

This uses the original preferences and stable-pair opposition. It does
not reverse the preference profile or assume stability survives reversal.
-/

namespace SmpMax.General

variable {n : ℕ} {I : Profile n} {μ ν : Matching n}

theorem crossing_forces_owner_better {m w : Fin n}
    (hp : StablePair I m w) (hμ : Stable I μ) (hν : Stable I ν)
    (hbefore : I.men m w < I.men m (μ m))
    (hcross : I.men m (ν m) ≤ I.men m w) :
    I.men (μ.symm w) (ν (μ.symm w)) < I.men (μ.symm w) (μ (μ.symm w)) := by
  have hold := (stable_pair_separation hp hμ).mp hbefore
  have hnew : I.women w m ≤ I.women w (ν.symm w) := by
    rcases lt_or_eq_of_le hcross with hlt | heq
    · exact (stable_pair_woman_prefers_of_worse hp hν hlt).le
    · have he := (I.men m).injective heq
      rw [← he, Equiv.symm_apply_apply]
  have h := hν.man_prefers_of_woman_prefers (m := μ.symm w) (w := w)
    (hold.trans_le hnew)
  simpa only [Equiv.apply_symm_apply] using h

noncomputable def betterPartners (I : Profile n) (μ : Matching n) (m : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => StablePair I m w ∧ I.men m w < I.men m (μ m))

noncomputable def nextBetterPartner (I : Profile n) (μ : Matching n) (m : Fin n) :
    Fin n := by
  classical
  exact if h : (betterPartners I μ m).Nonempty then
    Classical.choose ((betterPartners I μ m).exists_max_image (I.men m) h)
  else μ m

noncomputable def predecessorOwner (I : Profile n) (μ : Matching n) (m : Fin n) :
    Fin n := μ.symm (nextBetterPartner I μ m)

theorem nextBetterPartner_spec {m : Fin n} (h : (betterPartners I μ m).Nonempty) :
    StablePair I m (nextBetterPartner I μ m) ∧
    I.men m (nextBetterPartner I μ m) < I.men m (μ m) ∧
    ∀ w ∈ betterPartners I μ m, I.men m w ≤ I.men m (nextBetterPartner I μ m) := by
  classical
  simp only [nextBetterPartner, dif_pos h]
  have hs := Classical.choose_spec ((betterPartners I μ m).exists_max_image (I.men m) h)
  exact ⟨(Finset.mem_filter.mp hs.1).2.1, (Finset.mem_filter.mp hs.1).2.2, hs.2⟩

theorem predecessorOwner_ne_of_better {m : Fin n}
    (h : (betterPartners I μ m).Nonempty) : predecessorOwner I μ m ≠ m := by
  intro he
  have hew : nextBetterPartner I μ m = μ m := by
    simpa only [predecessorOwner, Equiv.apply_symm_apply] using congrArg μ he
  have hs := (nextBetterPartner_spec h).2.1
  rw [hew] at hs
  exact (lt_irrefl _) hs

theorem improving_propagates (hμ : Stable I μ) (hν : Stable I ν) {m : Fin n}
    (hm : I.men m (ν m) < I.men m (μ m)) :
    I.men (predecessorOwner I μ m) (ν (predecessorOwner I μ m)) <
      I.men (predecessorOwner I μ m) (μ (predecessorOwner I μ m)) := by
  classical
  have hmem : ν m ∈ betterPartners I μ m :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hν.stablePair m, hm⟩
  have hs := nextBetterPartner_spec ⟨ν m, hmem⟩
  exact crossing_forces_owner_better hs.1 hμ hν hs.2.1 (hs.2.2 _ hmem)

theorem compatible_predecessor_lower_barrier {m w : Fin n} {R : Finset (Fin n)}
    (hp : StablePair I m w) (hμ : Stable I μ) (hν : Compatible I μ R ν)
    (hbefore : I.men m w < I.men m (μ m))
    (hseen : predecessorOwner I μ (μ.symm w) ∈ R) :
    I.men m w < I.men m (ν m) := by
  by_contra hn
  have h1 := crossing_forces_owner_better hp hμ hν.1 hbefore (le_of_not_gt hn)
  have h2 := improving_propagates hμ hν.1 h1
  rw [hν.2 _ hseen] at h2
  exact (lt_irrefl _) h2

end SmpMax.General

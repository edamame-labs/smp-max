import SmpMax.General.LocalGapEvents
import SmpMax.General.BidirectionalGapSaving
import SmpMax.General.BidirectionalLogCertificate

/-!
# Expected directional losses from local events

The interface records geometric facts about a gap. Its hypotheses are
instantiated by the padded partner lists; no stochastic independence is used.
-/

namespace SmpMax.General.LocalGap

open FiniteProbability

variable {N : ℕ}

structure DirectionalData (N : ℕ) where
  label : Fin 7 → Fin N
  injective : Function.Injective label
  L : Equiv.Perm (Fin N) → ℕ
  R : Equiv.Perm (Fin N) → ℕ
  cap : Equiv.Perm (Fin N) → ℕ
  cap_le : ∀ π, cap π ≤ R π
  event_spec : ∀ j k (hj : j ≤ 2), k ≤ 3 → ∀ π ∈ oneEvent label j k hj,
    L π = j ∧ k ≤ R π

noncomputable def DirectionalData.loss (D : DirectionalData N) (π : Equiv.Perm (Fin N)) : ℝ :=
  Real.log (1 + (D.L π : ℝ) + D.R π) - Real.log (1 + (D.L π : ℝ) + D.cap π)

theorem DirectionalData.loss_nonneg (D : DirectionalData N) (π : Equiv.Perm (Fin N)) :
    0 ≤ D.loss π := by
  apply sub_nonneg.mpr
  apply Real.log_le_log (by positivity)
  have hc : (D.cap π : ℝ) ≤ D.R π := by exact_mod_cast D.cap_le π
  linarith

theorem DirectionalData.loss_onEvent_ge (D : DirectionalData N)
    {j k q : ℕ} (hj : j ≤ 2) (hk : k ≤ 3) (π : Equiv.Perm (Fin N))
    (he : π ∈ oneEvent D.label j k hj) (hq : D.cap π ≤ q) :
    Real.log (1 + (j : ℝ) + k) - Real.log (1 + (j : ℝ) + q) ≤ D.loss π := by
  obtain ⟨hL, hR⟩ := D.event_spec j k hj hk π he
  have h := BidirectionalGap.directional_loss_ge
    (L := (D.L π : ℝ)) (R := (D.R π : ℝ)) (r := (D.cap π : ℝ))
    (q := (q : ℝ)) (k := (k : ℝ)) (by positivity) (by positivity)
    (by exact_mod_cast hq) (by exact_mod_cast hR) (by positivity)
  simpa only [hL, DirectionalData.loss] using h

theorem DirectionalData.short_saving (D : DirectionalData N)
    (hshort : ∀ π, D.cap π ≤ 1) : shortSideSaving ≤ average D.loss := by
  classical
  let E₀ := oneEvent D.label 0 2 (by omega)
  let E₁ := oneEvent D.label 0 3 (by omega)
  let E₂ := oneEvent D.label 1 2 (by omega)
  have hpoint (π : Equiv.Perm (Fin N)) :
      (if π ∈ E₀ then logIncrement 1 else 0) +
      (if π ∈ E₁ then logIncrement 2 else 0) +
      (if π ∈ E₂ then logIncrement 2 else 0) ≤ D.loss π := by
    have hn := D.loss_nonneg π
    have hi := logIncrement_nonneg 1
    have h0 : π ∈ E₀ → logIncrement 1 ≤ D.loss π := by
      intro he
      have h := D.loss_onEvent_ge (by omega : 0 ≤ 2) (by omega : 2 ≤ 3) π he (hshort π)
      norm_num [logIncrement] at h ⊢
      exact h
    have h1 : π ∈ E₁ → logIncrement 1 + logIncrement 2 ≤ D.loss π := by
      intro he
      have h := D.loss_onEvent_ge (by omega : 0 ≤ 2) (by omega : 3 ≤ 3) π he (hshort π)
      norm_num [logIncrement] at h ⊢
      linarith
    have h2 : π ∈ E₂ → logIncrement 2 ≤ D.loss π := by
      intro he
      have h := D.loss_onEvent_ge (by omega : 1 ≤ 2) (by omega : 2 ≤ 3) π he (hshort π)
      norm_num [logIncrement] at h ⊢
      exact h
    have h02 : π ∈ E₀ → π ∈ E₂ → False := by
      intro he hf
      have ha := (D.event_spec 0 2 (by omega) (by omega) π he).1
      have hb := (D.event_spec 1 2 (by omega) (by omega) π hf).1
      omega
    have h12 : π ∈ E₁ → π ∈ E₂ → False := by
      intro he hf
      have ha := (D.event_spec 0 3 (by omega) (by omega) π he).1
      have hb := (D.event_spec 1 2 (by omega) (by omega) π hf).1
      omega
    split_ifs <;> grind
  have hh := average_mono hpoint
  rw [average_add, average_add, average_event, average_event, average_event] at hh
  have hp0 := probability_oneEvent D.label D.injective (by omega : 0 ≤ 2) (by omega : 2 ≤ 3)
  have hp1 := probability_oneEvent D.label D.injective (by omega : 0 ≤ 2) (by omega : 3 ≤ 3)
  have hp2 := probability_oneEvent D.label D.injective (by omega : 1 ≤ 2) (by omega : 2 ≤ 3)
  change probability E₀ = _ at hp0
  change probability E₁ = _ at hp1
  change probability E₂ = _ at hp2
  rw [hp0, hp1, hp2] at hh
  norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_ofNat, zero_add] at hh
  unfold shortSideSaving
  linarith

theorem DirectionalData.propagation_events (D : DirectionalData N) (u : Fin N)
    {q J : ℕ} (hq : q ≤ 1) (hJ : J ≤ 3)
    (hcap : ∀ π, π u < π (D.label 0) → D.cap π ≤ q) :
    (∑ j : Fin J, probability (twoEvent D.label u j.val (q + 1) (by omega)) *
      logIncrement (j.val + q)) ≤ average D.loss := by
  classical
  apply disjoint_events_average
  · exact D.loss_nonneg
  · intro j _ π hπ
    obtain ⟨hu, he⟩ := (mem_twoEvent D.label u π j.val (q + 1) (by omega)).mp hπ
    have h := D.loss_onEvent_ge (by omega : j.val ≤ 2) (by omega : q + 1 ≤ 3)
      π he (hcap π hu)
    have heq : Real.log (1 + (j.val : ℝ) + (q + 1 : ℕ)) -
        Real.log (1 + (j.val : ℝ) + q) = logIncrement (j.val + q) := by
      unfold logIncrement
      push_cast
      congr 1 <;> congr 1 <;> ring
    rw [heq] at h
    exact h
  · intro i _ j _ π hi hj
    have hi' := (D.event_spec i.val (q + 1) (by omega) (by omega) π
      ((mem_twoEvent D.label u π i.val (q + 1) (by omega)).mp hi).2).1
    have hj' := (D.event_spec j.val (q + 1) (by omega) (by omega) π
      ((mem_twoEvent D.label u π j.val (q + 1) (by omega)).mp hj).2).1
    exact Fin.ext (hi'.symm.trans hj')

theorem DirectionalData.first_step_saving (D : DirectionalData N) (u : Fin N)
    (hu0 : u ≠ D.label 0) (hu1 : u ≠ D.label 1)
    (hcap : ∀ π, π u < π (D.label 0) → D.cap π ≤ 0) :
    BidirectionalLogCertificate.firstStepSaving ≤ average D.loss := by
  classical
  have h := D.propagation_events u (q := 0) (J := 2) (by omega) (by omega) hcap
  simp only [Fin.sum_univ_two, Nat.add_zero, Fin.val_zero, Fin.val_one] at h
  have hp0 := probability_twoEvent D.label D.injective u hu0
    (by omega : 0 ≤ 2) (by omega : 1 ≤ 3)
  have hp1 := probability_twoEvent D.label D.injective u hu0
    (by omega : 1 ≤ 2) (by omega : 1 ≤ 3)
  simp only [afterLabels_01, afterLabels_11, Finset.mem_singleton, Finset.mem_insert,
    hu1, false_or, boundary_zero, boundary_one] at hp0 hp1
  by_cases h4 : u = D.label 4
  · subst u
    norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1
    rw [hp0, hp1] at h
    have hb := BidirectionalLogCertificate.firstStepSaving_le_first_coincidence
    norm_num [logIncrement] at h
    linarith
  · by_cases h5 : u = D.label 5
    · rw [if_neg h4] at hp0
      rw [if_pos h5] at hp1
      norm_num at hp0 hp1
      rw [hp0, hp1] at h
      have hn := logIncrement_nonneg 1
      unfold BidirectionalLogCertificate.firstStepSaving
      norm_num [logIncrement] at h hn ⊢
      linarith
    · rw [if_neg h4] at hp0
      rw [if_neg h5, if_neg h4] at hp1
      norm_num at hp0 hp1
      rw [hp0, hp1] at h
      unfold BidirectionalLogCertificate.firstStepSaving
      norm_num [logIncrement] at h ⊢
      linarith

theorem DirectionalData.second_step_saving (D : DirectionalData N) (u : Fin N)
    (hu0 : u ≠ D.label 0) (hu1 : u ≠ D.label 1) (hu2 : u ≠ D.label 2)
    (hcap : ∀ π, π u < π (D.label 0) → D.cap π ≤ 1) :
    BidirectionalLogCertificate.saving ≤ average D.loss := by
  classical
  have h := D.propagation_events u (q := 1) (J := 3) (by omega) (by omega) hcap
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one] at h
  norm_num only [Fin.val_two, Fin.val_ofNat, Nat.reduceMod, Nat.reduceAdd] at h
  have hp0 := probability_twoEvent D.label D.injective u hu0
    (by omega : 0 ≤ 2) (by omega : 2 ≤ 3)
  have hp1 := probability_twoEvent D.label D.injective u hu0
    (by omega : 1 ≤ 2) (by omega : 2 ≤ 3)
  have hp2 := probability_twoEvent D.label D.injective u hu0
    (by omega : 2 ≤ 2) (by omega : 2 ≤ 3)
  simp only [afterLabels_02, afterLabels_12, afterLabels_22,
    Finset.mem_singleton, Finset.mem_insert, hu1, hu2, false_or,
    boundary_zero, boundary_one, boundary_two] at hp0 hp1 hp2
  by_cases h4 : u = D.label 4
  · subst u
    norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1 hp2
    rw [hp0, hp1, hp2] at h
    have hb := BidirectionalLogCertificate.saving_le_first_coincidence
    linarith
  · by_cases h5 : u = D.label 5
    · subst u
      norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1 hp2
      rw [hp0, hp1, hp2] at h
      have hb := BidirectionalLogCertificate.saving_le_second_coincidence
      linarith
    · by_cases h6 : u = D.label 6
      · subst u
        norm_num [D.injective.eq_iff, Fin.ext_iff] at hp0 hp1 hp2
        rw [hp0, hp1, hp2] at h
        have hb := BidirectionalLogCertificate.saving_le_third_coincidence
        linarith
      · rw [if_neg h4] at hp0
        rw [if_neg h5, if_neg h4] at hp1
        rw [if_neg h6, if_neg (by simp [h4, h5])] at hp2
        norm_num at hp0 hp1 hp2
        rw [hp0, hp1, hp2] at h
        rw [← BidirectionalLogCertificate.secondStepSaving_eq]
        linarith

end SmpMax.General.LocalGap

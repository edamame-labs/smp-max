import SmpMax.General.SuccessorCharging

/-!
# Charging exceptions while retaining a joint directional saving

The extra noncycle margin pays for a missing joint bonus both at the
noncycle vertex and at the at-most-two exceptions charging it.
-/

namespace SmpMax.General.SuccessorCharging

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem local_joint_charge_bound (g : α → α) (D : Finset α)
    (s : α → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hzero : ∀ m, 0 ≤ s m) (hbase : ∀ m, m ∉ D → δ ≤ s m)
    (hbad : ∀ m, g (g m) ≠ m → 3 * (δ + ε) ≤ s m) (m : α) :
    δ + (if g (g m) ≠ m then 2 * δ + 3 * ε else 0) ≤
      s m + (if m ∈ D then δ else 0) := by
  classical
  by_cases hb : g (g m) ≠ m
  · have h := hbad m hb
    rw [if_pos hb]
    split_ifs <;> linarith
  · by_cases hd : m ∈ D
    · rw [if_neg hb, if_pos hd]
      linarith [hzero m]
    · rw [if_neg hb, if_neg hd]
      simpa only [add_zero] using hbase m hd

theorem sum_joint_saving_ge (g₀ g₁ b₀ b₁ : α → α) (D₀ D₁ : Finset α)
    (hD₀ : ∀ m ∈ D₀, Exceptional g₀ b₀ m)
    (hD₁ : ∀ m ∈ D₁, Exceptional g₁ b₁ m)
    (s₀ s₁ S : α → ℝ) (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hzero₀ : ∀ m, 0 ≤ s₀ m) (hzero₁ : ∀ m, 0 ≤ s₁ m)
    (hbase₀ : ∀ m, m ∉ D₀ → δ ≤ s₀ m)
    (hbase₁ : ∀ m, m ∉ D₁ → δ ≤ s₁ m)
    (hbad₀ : ∀ m, g₀ (g₀ m) ≠ m → 3 * (δ + ε) ≤ s₀ m)
    (hbad₁ : ∀ m, g₁ (g₁ m) ≠ m → 3 * (δ + ε) ≤ s₁ m)
    (hS : ∀ m, s₀ m + s₁ m ≤ S m)
    (hjoint : ∀ m, m ∉ D₀ → m ∉ D₁ → g₀ (g₀ m) = m → g₁ (g₁ m) = m →
      2 * δ + ε ≤ S m) :
    (Fintype.card α : ℝ) * (2 * δ + ε) ≤ ∑ m, S m := by
  classical
  let B₀ := Finset.univ.filter (fun m => g₀ (g₀ m) ≠ m)
  let B₁ := Finset.univ.filter (fun m => g₁ (g₁ m) ≠ m)
  have hpoint (m : α) :
      2 * δ + ε + (if m ∈ B₀ then 2 * (δ + ε) else 0) +
        (if m ∈ B₁ then 2 * (δ + ε) else 0) ≤
      S m + (if m ∈ D₀ then δ + ε else 0) + (if m ∈ D₁ then δ + ε else 0) := by
    have h₀ := local_joint_charge_bound g₀ D₀ s₀ hδ hzero₀ hbase₀ hbad₀ m
    have h₁ := local_joint_charge_bound g₁ D₁ s₁ hδ hzero₁ hbase₁ hbad₁ m
    have hs := hS m
    have hb₀ : m ∈ B₀ ↔ g₀ (g₀ m) ≠ m := by simp [B₀]
    have hb₁ : m ∈ B₁ ↔ g₁ (g₁ m) ≠ m := by simp [B₁]
    simp only [hb₀, hb₁]
    split_ifs at h₀ h₁ ⊢
    all_goals first
      | linarith
      | have hj := hjoint m (by assumption) (by assumption) (by tauto) (by tauto)
        linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun m _ => hpoint m)
  simp only [Finset.sum_add_distrib] at hsum
  have hind (E : Finset α) (c : ℝ) :
      (∑ m : α, if m ∈ E then c else 0) = (E.card : ℝ) * c := by
    rw [← Finset.sum_filter]
    simp
  rw [hind B₀, hind B₁, hind D₀, hind D₁] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hc₀ : (D₀.card : ℝ) ≤ 2 * B₀.card := by
    exact_mod_cast card_exceptions_le_twice_noncycles g₀ b₀ D₀ hD₀
  have hc₁ : (D₁.card : ℝ) ≤ 2 * B₁.card := by
    exact_mod_cast card_exceptions_le_twice_noncycles g₁ b₁ D₁ hD₁
  have hp₀ := mul_le_mul_of_nonneg_right hc₀ (add_nonneg hδ hε)
  have hp₁ := mul_le_mul_of_nonneg_right hc₁ (add_nonneg hδ hε)
  nlinarith

end SmpMax.General.SuccessorCharging

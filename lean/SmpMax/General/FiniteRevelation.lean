import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Finite counting by successive coordinate revelation

This is the finite conditional-support counting inequality used in
Palmer and Palvolgyi, Lemma 4. We prove it by partitioning a finite
family into full coordinate fibers, rather than introducing conditional
expectations. All logarithms are natural.
-/

namespace SmpMax.General.Revelation

open Finset

variable {α β : Type*} [DecidableEq β]

/-- A full fiber, keeping every outcome consistent with the revealed value. -/
def fiber (s : Finset α) (f : α → β) (b : β) : Finset α :=
  s.filter (fun x => f x = b)

/-- The log support cost of revealing the listed coordinates in order. -/
noncomputable def cost : List (α → β) → Finset α → α → ℝ
  | [], _, _ => 0
  | f :: fs, s, x => Real.log (s.image f).card + cost fs (fiber s f (f x)) x

/-- The coordinate list distinguishes all outcomes of the family. -/
def Separates (fs : List (α → β)) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, (∀ f ∈ fs, f x = f y) → x = y

omit [DecidableEq β] in
/-- Jensen's inequality for the positive masses of a finite partition. -/
theorem partition_log_bound {s : Finset β} (hs : s.Nonempty) (w : β → ℝ)
    (hw : ∀ b ∈ s, 0 < w b) :
    (∑ b ∈ s, w b) * Real.log (∑ b ∈ s, w b) ≤
      (∑ b ∈ s, w b) * Real.log s.card + ∑ b ∈ s, w b * Real.log (w b) := by
  have hk : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hn : 0 < ∑ b ∈ s, w b := Finset.sum_pos hw hs
  have hweights : ∑ _b ∈ s, (s.card : ℝ)⁻¹ = 1 := by simp [ne_of_gt hk]
  have hj := Real.convexOn_mul_log.map_sum_le
    (t := s) (w := fun _ => (s.card : ℝ)⁻¹) (p := w)
    (fun _ _ => inv_nonneg.mpr hk.le) hweights (fun b hb => (hw b hb).le)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hmul := mul_le_mul_of_nonneg_left hj hk.le
  rw [Real.log_mul (inv_ne_zero hk.ne') hn.ne', Real.log_inv] at hmul
  have hc : (s.card : ℝ) * (s.card : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hk.ne'
  simp only [← mul_assoc, hc, one_mul] at hmul
  nlinarith

/-- The one-coordinate entropy inequality, expressed entirely with finite sums. -/
theorem one_step (s : Finset α) (f : α → β) :
    (s.card : ℝ) * Real.log s.card ≤
      (s.card : ℝ) * Real.log (s.image f).card +
        ∑ x ∈ s, Real.log (fiber s f (f x)).card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [fiber]
  have hpos : ∀ b ∈ s.image f, 0 < ((fiber s f b).card : ℝ) := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have : 0 < (fiber s f (f x)).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    exact_mod_cast this
  have hsum : ∑ b ∈ s.image f, ((fiber s f b).card : ℝ) = s.card := by
    exact_mod_cast (Finset.card_eq_sum_card_image f s).symm
  have hweighted : ∑ b ∈ s.image f,
      ((fiber s f b).card : ℝ) * Real.log (fiber s f b).card =
      ∑ x ∈ s, Real.log (fiber s f (f x)).card := by
    have h := Finset.sum_fiberwise_of_maps_to' (s := s) (t := s.image f)
      (fun x hx => Finset.mem_image_of_mem f hx)
      (fun b => Real.log (fiber s f b).card)
    simpa only [fiber, Finset.sum_const, nsmul_eq_mul] using h
  have h := partition_log_bound (hs.image f) (fun b => ((fiber s f b).card : ℝ)) hpos
  rwa [hsum, hweighted] at h

/-- A coordinate list identifying each outcome bounds the logarithm of the family size.
Dividing by `s.card` when nonempty gives the uniform average log-support bound. -/
theorem count_le_sum_cost (fs : List (α → β)) (s : Finset α)
    (hsep : Separates fs s) :
    (s.card : ℝ) * Real.log s.card ≤ ∑ x ∈ s, cost fs s x := by
  induction fs generalizing s with
  | nil =>
    have hsub : (s : Set α).Subsingleton := fun x hx y hy => hsep x hx y hy (by simp)
    have hcard : s.card = 0 ∨ s.card = 1 := by
      have := Finset.card_le_one.mpr hsub
      omega
    rcases hcard with h | h <;> simp [cost, h]
  | cons f fs ih =>
    have hfsep : ∀ b, Separates fs (fiber s f b) := by
      intro b x hx y hy hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      apply hsep x hx'.1 y hy'.1
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hx'.2.trans hy'.2.symm
      · exact hxy g hg
    have hfiber : ∑ x ∈ s, Real.log (fiber s f (f x)).card ≤
        ∑ x ∈ s, cost fs (fiber s f (f x)) x := by
      have hb := Finset.sum_le_sum (s := s.image f)
        (fun b _ => ih (fiber s f b) (hfsep b))
      have hleft : ∑ b ∈ s.image f,
          ((fiber s f b).card : ℝ) * Real.log (fiber s f b).card =
          ∑ x ∈ s, Real.log (fiber s f (f x)).card := by
        have h := Finset.sum_fiberwise_of_maps_to' (s := s) (t := s.image f)
          (fun x hx => Finset.mem_image_of_mem f hx)
          (fun b => Real.log (fiber s f b).card)
        simpa only [fiber, Finset.sum_const, nsmul_eq_mul] using h
      rw [hleft] at hb
      have hright : (∑ b ∈ s.image f, ∑ x ∈ fiber s f b, cost fs (fiber s f b) x) =
          ∑ x ∈ s, cost fs (fiber s f (f x)) x := by
        calc
          _ = ∑ b ∈ s.image f, ∑ x ∈ fiber s f b,
              cost fs (fiber s f (f x)) x := by
                apply Finset.sum_congr rfl
                intro b _
                apply Finset.sum_congr rfl
                intro x hx
                rw [(Finset.mem_filter.mp hx).2]
          _ = _ := Finset.sum_fiberwise_of_maps_to
            (fun x hx => Finset.mem_image_of_mem f hx) _
      rw [hright] at hb
      exact hb
    calc
      _ ≤ (s.card : ℝ) * Real.log (s.image f).card +
          ∑ x ∈ s, Real.log (fiber s f (f x)).card := one_step s f
      _ ≤ (s.card : ℝ) * Real.log (s.image f).card +
          ∑ x ∈ s, cost fs (fiber s f (f x)) x := add_le_add le_rfl hfiber
      _ = _ := by simp only [cost, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

end SmpMax.General.Revelation

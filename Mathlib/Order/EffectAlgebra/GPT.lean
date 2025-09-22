/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.EffectAlgebra.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Generalized Probabilistic Theories (GPTs)

GPTs using weak states that trade additivity for well-defined tensor products.

## Implementation status

We use weak (non-additive) states to avoid the paradox that additive
product states cannot exist on minimal tensor products.

## Main definitions

* `WeakState`: States without additivity requirement
* `convexCombination`: Convex combinations of weak states
* `EffectSpace`: Structure combining effects and weak states
* `ClassicalSystem`: Classical probability as a GPT
* `classicalProductState`: Product states for classical systems

## Implementation notes

Weak states (no additivity) give well-defined tensor products.
Tradeoff: lose additivity, gain tensor products.

## References

* [Barnum and Wilce, *Information processing in convex operational theories*][barnum2011]
* [Hardy, *Quantum Theory From Five Reasonable Axioms*][hardy2001]
* [Coecke and Kissinger, *Picturing Quantum Processes*][coecke2017]

## Tags

generalized probabilistic theory, GPT, effect algebra, weak states, no-signaling
-/

open EffectAlgebra Finset BigOperators

/-! ### Weak States (No Additivity Requirement) -/

/-- Weak state: assigns probabilities without additivity.
Allows tensor products. -/
structure WeakState (E : Type*) [EffectAlgebra E] [OrderTop E] where
  /-- State functional -/
  val : E → ℝ
  /-- Non-negative -/
  nonneg : ∀ e, 0 ≤ val e
  /-- Normalized -/
  normalized : val ⊤ = 1

namespace WeakState

variable {E : Type*} [EffectAlgebra E] [OrderTop E]

/-- Convex combination -/
def convexCombination (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (s t : WeakState E) : WeakState E where
  val e := r * s.val e + (1 - r) * t.val e
  nonneg e := add_nonneg
    (mul_nonneg hr.1 (s.nonneg e))
    (mul_nonneg (sub_nonneg.mpr hr.2) (t.nonneg e))
  normalized := by simp [s.normalized, t.normalized]

theorem convexCombination_val (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (s t : WeakState E) (e : E) :
    (convexCombination r hr s t).val e = r * s.val e + (1 - r) * t.val e := rfl

theorem convexCombination_zero (s t : WeakState E) (e : E) :
    (convexCombination 0 ⟨le_refl 0, zero_le_one⟩ s t).val e = t.val e := by
  simp [convexCombination_val]

theorem convexCombination_one (s t : WeakState E) (e : E) :
    (convexCombination 1 ⟨zero_le_one, le_refl 1⟩ s t).val e = s.val e := by
  simp [convexCombination_val]

end WeakState

/-! ### Effect Spaces with Weak States -/

/-- Effect space: algebra plus convex state set -/
structure EffectSpace where
  /-- Effect algebra -/
  Effects : Type*
  /-- EffectAlgebra instance -/
  [ea : EffectAlgebra Effects]
  /-- OrderTop instance -/
  [top : OrderTop Effects]
  /-- Convex state set -/
  States : Set (WeakState Effects)
  /-- Non-empty states -/
  states_nonempty : States.Nonempty
  /-- Convex state set -/
  states_convex : ∀ s ∈ States, ∀ t ∈ States, ∀ r (hr : 0 ≤ r ∧ r ≤ 1),
    WeakState.convexCombination r hr s t ∈ States
  /-- States distinguish effects -/
  separating : ∀ e₁ e₂ : Effects,
    (∀ s ∈ States, s.val e₁ = s.val e₂) → e₁ = e₂

namespace EffectSpace

variable (E : EffectSpace)

instance : EffectAlgebra E.Effects := E.ea
instance : OrderTop E.Effects := E.top

end EffectSpace

/-! ### Classical Systems -/

/-- Classical system: states are distributions on n outcomes,
effects are subsets. -/
def ClassicalSystem (n : ℕ) (hn : n > 0) : EffectSpace where
  Effects := Fin n → Bool
  States := { s : WeakState (Fin n → Bool) |
    ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
    ∀ f, s.val f = ∑ i, if f i then p i else 0 }
  states_nonempty := by
    -- Use uniform distribution
    let p : Fin n → ℝ := fun _ => 1 / n
    let s : WeakState (Fin n → Bool) := {
      val := fun f => ∑ i, if f i then p i else 0
      nonneg := fun f => by
        apply Finset.sum_nonneg
        intro i _
        split_ifs
        · exact div_nonneg zero_le_one (Nat.cast_nonneg n)
        · exact le_refl 0
      normalized := by
        have : ∀ i, (⊤ : Fin n → Bool) i = true := fun i => rfl
        simp only [this, ite_true, p, Finset.sum_const, Finset.card_fin]
        rw [nsmul_eq_mul, mul_one_div, div_self (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
    }
    use s
    simp only [Set.mem_setOf_eq]
    use p
    constructor
    · intro i
      exact div_nonneg zero_le_one (Nat.cast_nonneg n)
    constructor
    · simp only [p, Finset.sum_const, Finset.card_fin]
      rw [nsmul_eq_mul, mul_one_div, div_self (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
    · intro f
      rfl
  states_convex := by
    intros s hs t ht r hr
    obtain ⟨ps, hps_nonneg, hps_sum, hps_eq⟩ := hs
    obtain ⟨pt, hpt_nonneg, hpt_sum, hpt_eq⟩ := ht
    simp only [Set.mem_setOf_eq]
    use fun i => r * ps i + (1 - r) * pt i
    constructor
    · intro i
      exact add_nonneg (mul_nonneg hr.1 (hps_nonneg i))
                       (mul_nonneg (sub_nonneg.mpr hr.2) (hpt_nonneg i))
    constructor
    · calc ∑ i, (r * ps i + (1 - r) * pt i)
        = ∑ i, r * ps i + ∑ i, (1 - r) * pt i := by rw [Finset.sum_add_distrib]
      _ = r * ∑ i, ps i + (1 - r) * ∑ i, pt i := by simp only [← Finset.mul_sum]
      _ = r * 1 + (1 - r) * 1 := by rw [hps_sum, hpt_sum]
      _ = 1 := by simp_all
    · intro f
      simp only [WeakState.convexCombination_val]
      rw [hps_eq, hpt_eq]
      have eq1 : r * ∑ i, (if f i then ps i else 0) = ∑ i, r * (if f i then ps i else 0) := by
        rw [← Finset.mul_sum]
      have eq2 : (1 - r) * ∑ i, (if f i then pt i else 0) =
          ∑ i, (1 - r) * (if f i then pt i else 0) := by
        rw [← Finset.mul_sum]
      rw [eq1, eq2, ← Finset.sum_add_distrib]
      congr 1
      ext i
      split_ifs <;> simp_all
  separating := by
    intros f₁ f₂ h
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, f₁ i ≠ f₂ i := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    -- Point mass at i
    let δᵢ : WeakState (Fin n → Bool) := ⟨
      fun f => if f i then 1 else 0,
      fun f => by
        by_cases hf : f i <;> simp [hf],
      by simp⟩
    -- Show δᵢ is a valid state in ClassicalSystem
    have hδᵢ : δᵢ ∈ { s : WeakState (Fin n → Bool) |
        ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
        ∀ f, s.val f = ∑ i, if f i then p i else 0 } := by
      simp only [Set.mem_setOf_eq]
      use fun j => if j = i then 1 else 0
      constructor
      · intro j
        by_cases hj : j = i <;> simp [hj]
      constructor
      · simp
      · intro f
        simp only [δᵢ]
        by_cases hf : f i
        · simp [hf]
          rw [Finset.sum_eq_single i]
          · simp [hf]
          · intro j _ hj
            simp [hj]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        · simp [hf]
          symm
          apply Finset.sum_eq_zero
          intro j _
          by_cases hj : j = i
          · subst hj
            simp [hf]
          · simp [hj]
    -- δᵢ distinguishes f₁ and f₂
    have hdist : δᵢ.val f₁ ≠ δᵢ.val f₂ := by
      simp only [δᵢ]
      intro heq
      by_cases h1 : f₁ i <;> by_cases h2 : f₂ i
      · simp [h1, h2] at heq
        have : f₁ i = f₂ i := by simp [h1, h2]
        exact hi this
      · simp [h1, h2] at heq
      · simp [h1, h2] at heq
      · simp [h1, h2] at heq
        have : f₁ i = f₂ i := by simp [h1, h2]
        exact hi this
    exact hdist (h δᵢ hδᵢ)

/-! ### Product States for Classical Systems -/

/-- Product state -/
def classicalProductState {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (s₁ : (ClassicalSystem n hn).States) (s₂ : (ClassicalSystem m hm).States) :
    WeakState ((Fin n → Bool) × (Fin m → Bool)) where
  val := fun (f₁, f₂) => s₁.1.val f₁ * s₂.1.val f₂
  nonneg := fun (f₁, f₂) => mul_nonneg (s₁.1.nonneg f₁) (s₂.1.nonneg f₂)
  normalized := by
    have h₁ : s₁.1.val ⊤ = 1 := s₁.1.normalized
    have h₂ : s₂.1.val ⊤ = 1 := s₂.1.normalized
    simp only [h₁, h₂, mul_one]

/-- No-signaling -/
theorem classicalProductState_noSignaling {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (s₁ : (ClassicalSystem n hn).States) (s₂ : (ClassicalSystem m hm).States) :
    let s := classicalProductState hn hm s₁ s₂
    (∀ f₁, s.val (f₁, ⊤) = s₁.1.val f₁) ∧
    (∀ f₂, s.val (⊤, f₂) = s₂.1.val f₂) := by
  simp only [classicalProductState]
  constructor
  · intro f₁
    simp only [s₂.1.normalized, mul_one]
  · intro f₂
    simp only [s₁.1.normalized, one_mul]

/-- Product states are valid -/
theorem classicalProductState_valid {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (s₁ : (ClassicalSystem n hn).States) (s₂ : (ClassicalSystem m hm).States) :
    ∃ p : Fin n → ℝ, ∃ q : Fin m → ℝ,
      (∀ i, 0 ≤ p i) ∧ (∀ j, 0 ≤ q j) ∧ (∑ i, p i = 1) ∧ (∑ j, q j = 1) ∧
      ∀ f₁ f₂, (classicalProductState hn hm s₁ s₂).val (f₁, f₂) =
        (∑ i, if f₁ i then p i else 0) * (∑ j, if f₂ j then q j else 0) := by
  obtain ⟨p, hp_nonneg, hp_sum, hp_eq⟩ := s₁.2
  obtain ⟨q, hq_nonneg, hq_sum, hq_eq⟩ := s₂.2
  use p, q
  refine ⟨hp_nonneg, hq_nonneg, hp_sum, hq_sum, ?_⟩
  intros f₁ f₂
  simp only [classicalProductState]
  rw [hp_eq, hq_eq]

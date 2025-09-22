/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic

/-!
# Partial Commutative Monoids

Partial Commutative Monoids (PCMs) are the foundation of effect algebras and categorical
probability. They capture partiality: operations only defined when results remain valid.

## Main definitions

* `PartialCommMonoid`: PCM with partial addition on orthogonal elements
* `pcmOfEffectAlgebra`: Every generalized Boolean algebra gives a PCM

## Implementation notes

We use dependent types for partial operations to ensure type safety.
The complex associativity axiom encodes that coarse-graining order doesn't matter.

## References

* [Jacobs, *New directions in categorical logic*][jacobs2012]
* [Foulis and Bennett, *Effect algebras and unsharp quantum logics*][foulis1994]

## Tags

partial commutative monoid, effect algebra, orthogonality, partial operation
-/

/-- Orthogonality relation for PCM elements -/
class HasOrthogonal (M : Type*) where
  /-- The orthogonality relation -/
  rel : M → M → Prop

-- Define orthogonality notation
@[inherit_doc HasOrthogonal.rel]
infixl:50 " ⊥ " => HasOrthogonal.rel

set_option linter.unusedVariables false in
/-- Partial commutative monoid -/
class PartialCommMonoid (M : Type*) extends Zero M, HasOrthogonal M where
  /-- Partial addition of orthogonal elements -/
  padd : (x y : M) → (h : rel x y) → M

  /-- Orthogonality is symmetric -/
  orth_comm : ∀ (x y : M), rel x y → rel y x

  /-- Partial addition commutes -/
  padd_comm : ∀ (x y : M) (h : rel x y), padd x y h = padd y x (orth_comm x y h)

  /-- Complex associativity condition -/
  orth_assoc : ∀ (x y z : M) (h₁ : rel y z) (h₂ : rel x (padd y z h₁)),
    ∃ (hxy : rel x y), rel (padd x y hxy) z

  /-- Associativity of partial addition -/
  padd_assoc : ∀ (x y z : M) (h₁ : rel y z) (h₂ : rel x (padd y z h₁)),
    ∃ (hxy : rel x y) (hxyz : rel (padd x y hxy) z),
    padd x (padd y z h₁) h₂ = padd (padd x y hxy) z hxyz

  /-- Zero is orthogonal to everything -/
  zero_orth : ∀ (x : M), rel 0 x

  /-- Adding zero is identity -/
  zero_padd : ∀ (x : M), padd 0 x (zero_orth x) = x

-- Notation for partial addition
@[inherit_doc PartialCommMonoid.padd]
notation:65 x " ⊕[" h "] " y => PartialCommMonoid.padd x y h

namespace PartialCommMonoid

variable {M : Type*} [PartialCommMonoid M]

/-- Zero on the right -/
theorem orth_zero (x : M) : x ⊥ 0 :=
  PartialCommMonoid.orth_comm 0 x (PartialCommMonoid.zero_orth x)

/-- Adding zero on the right -/
theorem padd_zero (x : M) : PartialCommMonoid.padd x 0 (orth_zero x) = x := by
  rw [PartialCommMonoid.padd_comm x 0]
  exact PartialCommMonoid.zero_padd x

end PartialCommMonoid

/-- PCM structure from generalized Boolean algebra -/
instance pcmOfEffectAlgebra {α : Type*} [GeneralizedBooleanAlgebra α] :
    PartialCommMonoid α where
  zero := ⊥
  rel := Disjoint
  padd x y _ := x ⊔ y
  orth_comm _ _ := disjoint_comm.mp
  padd_comm x y _ := sup_comm x y
  orth_assoc x y z hyz hx_yz := by
    use Disjoint.mono_right le_sup_left hx_yz
    rw [disjoint_sup_left]
    exact ⟨Disjoint.mono_right le_sup_right hx_yz, hyz⟩
  padd_assoc x y z hyz hx_yz := by
    use Disjoint.mono_right le_sup_left hx_yz
    have hab_c : Disjoint (x ⊔ y) z := by
      rw [disjoint_sup_left]
      exact ⟨Disjoint.mono_right le_sup_right hx_yz, hyz⟩
    use hab_c
    simp only [sup_assoc]
  zero_orth _ := disjoint_bot_left
  zero_padd x := bot_sup_eq x

/-! ### Examples -/

namespace Examples

/-- The unit interval [0,1] forms a PCM -/
instance unitIntervalPCM : PartialCommMonoid (Set.Icc (0 : ℝ) 1) where
  zero := ⟨0, by simp⟩
  rel x y := x.val + y.val ≤ 1
  padd x y h := ⟨x.val + y.val, by
    constructor
    · exact add_nonneg x.2.1 y.2.1
    · exact h⟩
  orth_comm _ _ h := by simp [add_comm] at h ⊢; exact h
  padd_comm _ _ _ := by ext; simp [add_comm]
  orth_assoc x y z h₁ h₂ := by
    simp at h₁ h₂ ⊢
    constructor
    · grind only [= Set.mem_Icc, cases eager Subtype]
    · grind only [cases eager Subtype]
  padd_assoc x y z h₁ h₂ := by
    use ?_, ?_
    · simp at h₂ ⊢
      grind only [cases eager Subtype]
    · simp at h₁ h₂ ⊢
      grind only [= Set.mem_Icc, cases eager Subtype]
    · grind only [cases eager Subtype]
  zero_orth x := by
    change 0 + x.val ≤ 1
    simp only [zero_add]
    exact x.2.2
  zero_padd x := by
    ext
    change 0 + x.val = x.val
    simp only [zero_add]

end Examples

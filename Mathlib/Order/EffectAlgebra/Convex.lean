/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.EffectAlgebra.Basic
import Mathlib.Topology.UnitInterval

/-!
# Convex Effect Algebras

This file defines convex structures on effect algebras: scalar multiplication
by `[0,1]` and effect modules. These model mixtures of quantum effects.

## Main definitions

* `ConvexEffectAlgebra`: Effect algebra with scalar multiplication by `[0,1]`
* `EffectModule`: Effect algebra with scalar action by a semiring
* Convexity properties of state spaces

## References

* [Foulis and Bennett, *Effect algebras and unsharp quantum logics*][foulis1994]
* [Gudder, *Convex effect algebras*][gudder2005]

## Tags

effect algebra, convex structure, effect module, quantum logic
-/

open Order EffectAlgebra unitInterval

variable {α : Type*}

/-! ### Convex Effect Algebras -/

/-- Effect algebra with scalar multiplication by `[0,1]`.
Models probabilistic mixtures. -/
class ConvexEffectAlgebra (α : Type*) [EffectAlgebra α] [OrderTop α] where
  /-- Scalar multiplication by `[0,1]` -/
  smul : I → α → α
  /-- Zero scalar gives bottom -/
  smul_zero : ∀ a, smul 0 a = ⊥
  /-- Unit scalar is identity -/
  smul_one : ∀ a, smul 1 a = a
  /-- Preserves orthogonality -/
  smul_orthogonal : ∀ (r s : I) (a b : α),
    orthogonal a b → orthogonal (smul r a) (smul s b)
  /-- Distributes over orthogonal sums -/
  smul_oplus : ∀ (r : I) (a b : α) (hab : orthogonal a b),
    ∃ (h' : orthogonal (smul r a) (smul r b)),
      smul r (oplus a b hab) = oplus (smul r a) (smul r b) h'

namespace ConvexEffectAlgebra

variable [EffectAlgebra α] [OrderTop α] [ConvexEffectAlgebra α]

/-- Scalar multiplication notation -/
scoped notation:73 r " • " a => ConvexEffectAlgebra.smul r a

/-- Complement scalar `1 - r` -/
def comp (r : I) : I := ⟨1 - r.val, by
  constructor
  · exact sub_nonneg.mpr r.property.2
  · simp [r.property.1]⟩

/-- Convex combination -/
def convexComb (r : I) (a b : α) (hab : orthogonal a b) : α :=
  oplus (r • a) ((comp r) • b) (smul_orthogonal r (comp r) a b hab)

theorem convexComb_zero (a b : α) (hab : orthogonal a b) :
    convexComb 0 a b hab = b := by
  simp [convexComb, comp, smul_zero, smul_one, bot_oplus]

theorem convexComb_one (a b : α) (hab : orthogonal a b) :
    convexComb 1 a b hab = a := by
  simp [convexComb, comp, smul_one, smul_zero, oplus_bot]

end ConvexEffectAlgebra

/-! ### Effect Modules -/

/-- Effect modules: scalar multiplication by semirings -/
class EffectModule (α : Type*) [EffectAlgebra α] [OrderTop α] (R : Type*)
    [Semiring R] [PartialOrder R] where
  /-- Scalar multiplication -/
  smul : R → α → α
  /-- Preserves orthogonality -/
  smul_orthogonal : ∀ r a b, orthogonal a b →
    orthogonal (smul r a) (smul r b)
  /-- Distributes over sums -/
  smul_oplus : ∀ r a b h, smul r (oplus a b h) =
    oplus (smul r a) (smul r b) (smul_orthogonal r a b h)
  /-- Zero gives bottom -/
  smul_zero : ∀ a, smul 0 a = ⊥
  /-- One is identity -/
  smul_one : ∀ a, smul 1 a = a

namespace EffectModule

variable [EffectAlgebra α] [OrderTop α] {R : Type*} [Semiring R] [PartialOrder R]
variable [EffectModule α R]

/-- Notation for scalar multiplication in effect modules -/
scoped notation:73 r " •ₘ " a => EffectModule.smul r a

-- theorem smul_bot (r : R) : r •ₘ (⊥ : α) = ⊥ := by
--   sorry  -- Would require additional axioms about scalar multiplication

end EffectModule

/-! ### Convex Sets of States -/

/-- Convex combination of two effect states -/
def convexCombination [EffectAlgebra α] [OrderTop α]
    (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1)
    (s t : EffectState α) : EffectState α := {
  val := fun a => r * s.val a + (1 - r) * t.val a
  nonneg := fun a => add_nonneg
    (mul_nonneg hr.1 (s.nonneg a))
    (mul_nonneg (sub_nonneg.mpr hr.2) (t.nonneg a))
  normalized := by
    simp [s.normalized, t.normalized]
  additive := fun a b hab => by
    simp [s.additive a b hab, t.additive a b hab]
    ring
}

/-- The set of states on an effect algebra forms a convex set -/
theorem effectStates_convex [EffectAlgebra α] [OrderTop α] :
    ∀ (s t : EffectState α) (r : I),
      ∃ (st : EffectState α),
        st.val = fun a => r.val * s.val a + (1 - r.val) * t.val a := by
  intros s t r
  use {
    val := fun a => r.val * s.val a + (1 - r.val) * t.val a
    nonneg := fun a => by
      apply add_nonneg
      · exact mul_nonneg r.property.1 (s.nonneg a)
      · exact mul_nonneg (sub_nonneg.mpr r.property.2) (t.nonneg a)
    normalized := by
      simp [s.normalized, t.normalized]
    additive := fun a b hab => by
      simp only [s.additive a b hab, t.additive a b hab]
      ring
  }

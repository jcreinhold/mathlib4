/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Effect Algebras

This file defines effect algebras as `GeneralizedBooleanAlgebra` with
effect operations and notation. Effect algebras model quantum effects and
unsharp measurements.

Extensions for convex structures, sequential operations, and GPTs
appear in separate files.

## Main definitions

* `EffectAlgebra`: Type alias for `GeneralizedBooleanAlgebra`
* `EffectAlgebra.orthogonal`: Elements are disjoint (notation: `a ⊥ b`)
* `EffectAlgebra.oplus`: Sum of disjoint elements (notation: `a ⊕[h] b`)
* `EffectAlgebra.effectCompl`: Effect complement `⊤ \ a` (notation: `aᵉ`)
* `EffectState`: States on effect algebras (probability measures on effects)

## Main results

* The five Foulis-Bennett axioms hold for these operations
* `oplus_eq_sup`: For disjoint elements, `a ⊕[h] b = a ⊔ b`
* `orthogonal_self_iff`: An element is orthogonal to itself iff it equals bottom

## References

* [Foulis and Bennett, *Effect algebras and unsharp quantum logics*][foulis1994]

## Tags

effect algebra, generalized boolean algebra, quantum logic, partial operation
-/

open Order

variable {α : Type*}

/-- Effect algebras are generalized Boolean algebras with
    partial operations on orthogonal elements -/
abbrev EffectAlgebra (α : Type*) := GeneralizedBooleanAlgebra α

namespace EffectAlgebra

variable [EffectAlgebra α] [OrderTop α]

/-! ### Effect Algebra Operations -/

/-- Elements are orthogonal when disjoint -/
def orthogonal (a b : α) : Prop := Disjoint a b

/-- Sum of orthogonal elements. Only defined when `a` and `b` are orthogonal. -/
def oplus (a b : α) (h : orthogonal a b) : α :=
  have _ := h  -- Use orthogonality
  a ⊔ b

/-- Effect complement: `⊤ \ a` -/
def effectCompl (a : α) : α := ⊤ \ a

/-! ### Notation -/

@[inherit_doc] scoped notation:50 a " ⊥ " b => EffectAlgebra.orthogonal a b
@[inherit_doc] scoped notation:65 a " ⊕[" h "] " b => EffectAlgebra.oplus a b h
@[inherit_doc] scoped postfix:max "ᵉ" => EffectAlgebra.effectCompl

/-! ### The Five Foulis-Bennett Axioms -/

omit [OrderTop α] in
/-- EA1: Orthogonality commutes -/
theorem orthogonal_comm (a b : α) : (a ⊥ b) ↔ (b ⊥ a) :=
  disjoint_comm

omit [OrderTop α] in
/-- EA2: Orthogonal sum commutes -/
theorem oplus_comm (a b : α) (h : a ⊥ b) :
    oplus a b h = oplus b a ((orthogonal_comm a b).mp h) :=
  sup_comm a b

omit [OrderTop α] in
/-- EA3: Partial addition associates -/
theorem oplus_assoc (a b c : α) (hbc : b ⊥ c)
    (habc : a ⊥ oplus b c hbc) :
    ∃ (hab : a ⊥ b) (hab_c : (oplus a b hab) ⊥ c),
      oplus a (oplus b c hbc) habc = oplus (oplus a b hab) c hab_c := by
  -- a ⊥ b since a ⊥ (b ⊔ c)
  use Disjoint.mono_right le_sup_left habc
  -- (a ⊔ b) ⊥ c since both a and b are disjoint from c
  have hab_c : Disjoint (a ⊔ b) c := by
    rw [disjoint_sup_left]
    exact ⟨Disjoint.mono_right le_sup_right habc, hbc⟩
  use hab_c
  simp only [oplus, sup_assoc]

/-- EA4: Elements are orthogonal to their complements -/
theorem orthogonal_effectCompl (a : α) : a ⊥ aᵉ := by
  simp only [orthogonal, effectCompl]
  exact disjoint_sdiff_self_right

/-- EA5: Sum with complement gives top -/
theorem oplus_effectCompl (a : α) :
    oplus a aᵉ (orthogonal_effectCompl a) = ⊤ := by
  simp only [oplus, effectCompl]
  rw [sup_comm]
  exact sdiff_sup_cancel le_top

/-- EA6: Top orthogonal to a iff a = ⊥ -/
theorem orthogonal_top_iff (a : α) : (⊤ ⊥ a) ↔ (a = ⊥) := by
  simp only [orthogonal, disjoint_comm]
  letI : BoundedOrder α := BoundedOrder.mk
  rw [disjoint_top]

/-! ### Additional Properties -/

omit [OrderTop α] in
/-- Sum equals supremum -/
theorem oplus_eq_sup {a b : α} (h : a ⊥ b) :
    oplus a b h = a ⊔ b := rfl

omit [OrderTop α] in
/-- Bottom orthogonal to all -/
@[simp] theorem bot_orthogonal (a : α) : ⊥ ⊥ a :=
  disjoint_bot_left

omit [OrderTop α] in
@[simp] theorem orthogonal_bot (a : α) : a ⊥ ⊥ :=
  disjoint_bot_right

omit [OrderTop α] in
/-- Sum with bottom -/
theorem bot_oplus (a : α) (h : ⊥ ⊥ a := bot_orthogonal a) :
    (oplus ⊥ a) h = a := by
  unfold oplus
  rw [bot_sup_eq]

omit [OrderTop α] in
theorem oplus_bot (a : α) (h : a ⊥ ⊥ := orthogonal_bot a) :
    oplus a ⊥ h = a := by
  unfold oplus
  rw [sup_bot_eq]

/-- Double complement -/
theorem effectCompl_effectCompl (a : α) : aᵉᵉ = a := by
  simp only [effectCompl, sdiff_sdiff_right_self, inf_of_le_right le_top]

/-- Complement of bottom -/
@[simp] theorem effectCompl_bot : (⊥ : α)ᵉ = ⊤ := by
  simp only [effectCompl, sdiff_bot]

/-- Complement of top -/
@[simp] theorem effectCompl_top : (⊤ : α)ᵉ = ⊥ := by
  simp only [effectCompl, sdiff_self]

omit [OrderTop α] in
/-- Self-orthogonal iff bottom -/
theorem orthogonal_self_iff {a : α} : (a ⊥ a) ↔ (a = ⊥) := by
  simp only [orthogonal]
  exact disjoint_self

/-- Complement reverses order -/
theorem effectCompl_le_effectCompl {a b : α} (h : a ≤ b) : bᵉ ≤ aᵉ :=
  sdiff_le_sdiff_left h

omit [OrderTop α] in
/-- Order from orthogonal decomposition -/
theorem le_iff_exists_orthogonal_oplus {a b : α} : a ≤ b ↔
    ∃ (c : α) (h : a ⊥ c), oplus a c h = b := by
  constructor
  · intro hab
    refine ⟨b \ a, ?orthogonal, ?equation⟩
    case orthogonal =>
      exact disjoint_sdiff_self_right
    case equation =>
      simp [oplus]
      exact hab
  · -- If decomposition exists, then a ≤ b
    intro ⟨c, hac, heq⟩
    rw [← heq, oplus]
    exact le_sup_left

end EffectAlgebra

/-! ### States on Effect Algebras -/

/-- States assign probabilities to effects.
In GPTs, states are preparations and effects are measurements. -/
structure EffectState (α : Type*) [EffectAlgebra α] [OrderTop α] where
  /-- Map effects to probabilities -/
  val : α → ℝ
  /-- Non-negative values -/
  nonneg : ∀ a, 0 ≤ val a
  /-- Normalized to 1 -/
  normalized : val ⊤ = 1
  /-- Additive on orthogonal elements -/
  additive : ∀ a b (h : EffectAlgebra.orthogonal a b),
    val (EffectAlgebra.oplus a b h) = val a + val b

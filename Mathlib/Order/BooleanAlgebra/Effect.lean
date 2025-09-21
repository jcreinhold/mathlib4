/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Effect Algebra Operations on Generalized Boolean Algebras

This file shows that every `GeneralizedBooleanAlgebra` can be viewed as an effect algebra
by providing the appropriate operations and proving they satisfy the Foulis-Bennett axioms.

Effect algebras model quantum effects and unsharp measurements in quantum mechanics.
They are mathematically equivalent to `GeneralizedBooleanAlgebra`.

## Main definitions

* `GeneralizedBooleanAlgebra.orthogonal`: Elements are disjoint (notation: `a ⊥ b`)
* `GeneralizedBooleanAlgebra.oplus`: Sum of disjoint elements (notation: `a ⊕[h] b`)
* `GeneralizedBooleanAlgebra.effectCompl`: Effect complement `⊤ \ a` (notation: `aᵉ`)

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

namespace GeneralizedBooleanAlgebra

section EffectAlgebra

variable [GeneralizedBooleanAlgebra α] [OrderTop α]

/-! ### Effect Algebra Operations -/

/-- Elements are orthogonal when they are disjoint in the lattice sense -/
def orthogonal (a b : α) : Prop := Disjoint a b

/-- Sum of orthogonal elements is their supremum -/
def oplus (a b : α) (_ : orthogonal a b) : α := a ⊔ b

/-- Effect complement is the difference from top -/
def effectCompl (a : α) : α := ⊤ \ a

/-! ### Notation -/

scoped notation:50 a " ⊥ " b => GeneralizedBooleanAlgebra.orthogonal a b
scoped notation:65 a " ⊕[" h "] " b => GeneralizedBooleanAlgebra.oplus a b h
scoped postfix:max "ᵉ" => GeneralizedBooleanAlgebra.effectCompl

/-! ### The Five Foulis-Bennett Axioms -/

omit [OrderTop α] in
/-- EA1: Orthogonality is symmetric -/
theorem orthogonal_comm (a b : α) : (a ⊥ b) ↔ (b ⊥ a) :=
  disjoint_comm

omit [OrderTop α] in
/-- EA2: Commutativity of orthogonal sum -/
theorem oplus_comm (a b : α) (h : a ⊥ b) :
    oplus a b h = oplus b a ((orthogonal_comm a b).mp h) :=
  sup_comm a b

omit [OrderTop α] in
/-- EA3: Associativity condition for partial addition -/
theorem oplus_assoc (a b c : α) (hbc : b ⊥ c)
    (habc : a ⊥ oplus b c hbc) :
    ∃ (hab : a ⊥ b) (hab_c : (oplus a b hab) ⊥ c),
      oplus a (oplus b c hbc) habc = oplus (oplus a b hab) c hab_c := by
  -- hab : a ⊥ b follows from a being disjoint from b ⊔ c
  use Disjoint.mono_right le_sup_left habc
  -- hab_c : (a ⊔ b) ⊥ c follows from both a and b being disjoint from c
  have hab_c : Disjoint (a ⊔ b) c := by
    rw [disjoint_sup_left]
    exact ⟨Disjoint.mono_right le_sup_right habc, hbc⟩
  use hab_c
  -- The equality follows from sup_assoc
  simp only [oplus, sup_assoc]

/-- EA4: Every element is orthogonal to its effect complement -/
theorem orthogonal_effectCompl (a : α) : a ⊥ aᵉ := by
  simp only [orthogonal, effectCompl]
  exact disjoint_sdiff_self_right

/-- EA5: Sum with effect complement gives top -/
theorem oplus_effectCompl (a : α) :
    oplus a aᵉ (orthogonal_effectCompl a) = ⊤ := by
  simp only [oplus, effectCompl]
  rw [sup_comm]
  exact sdiff_sup_cancel le_top

/-- EA6: Characterization of bottom via orthogonality with top -/
theorem orthogonal_top_iff (a : α) : (⊤ ⊥ a) ↔ (a = ⊥) := by
  simp only [orthogonal, disjoint_comm]
  letI : BoundedOrder α := BoundedOrder.mk
  rw [disjoint_top]

/-! ### Additional Properties -/

omit [OrderTop α] in
/-- Orthogonal sum equals supremum -/
theorem oplus_eq_sup {a b : α} (h : a ⊥ b) :
    oplus a b h = a ⊔ b := rfl

omit [OrderTop α] in
/-- Bottom is orthogonal to everything -/
@[simp] theorem bot_orthogonal (a : α) : ⊥ ⊥ a :=
  disjoint_bot_left

omit [OrderTop α] in
@[simp] theorem orthogonal_bot (a : α) : a ⊥ ⊥ :=
  disjoint_bot_right

omit [OrderTop α] in
/-- Orthogonal sum with bottom -/
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
/-- An element is orthogonal to itself iff it is bottom -/
theorem orthogonal_self_iff {a : α} : (a ⊥ a) ↔ (a = ⊥) := by
  simp only [orthogonal]
  exact disjoint_self

/-- Orthocomplement is antitone -/
theorem effectCompl_le_effectCompl {a b : α} (h : a ≤ b) : bᵉ ≤ aᵉ :=
  sdiff_le_sdiff_left h

omit [OrderTop α] in
/-- Order structure induced by effect algebra -/
theorem le_iff_exists_orthogonal_oplus {a b : α} : a ≤ b ↔
    ∃ (c : α) (h : a ⊥ c), oplus a c h = b := by
  constructor
  · -- Forward direction: if a ≤ b, use c = b \ a
    intro hab
    refine ⟨b \ a, ?orthogonal, ?equation⟩
    case orthogonal =>
      exact disjoint_sdiff_self_right
    case equation =>
      simp [oplus]
      exact hab
  · -- Backward direction: if decomposition exists, then a ≤ b
    intro ⟨c, hac, heq⟩
    rw [← heq, oplus]
    exact le_sup_left

end EffectAlgebra

end GeneralizedBooleanAlgebra

/-! ### Examples -/

section Examples

open GeneralizedBooleanAlgebra

/-- Any `GeneralizedBooleanAlgebra` with a top element can be viewed as an effect algebra -/
example [GeneralizedBooleanAlgebra α] [OrderTop α] (a b : α) (h : orthogonal a b) :
  oplus a b h = a ⊔ b := rfl

/-- Finsets form an effect algebra -/
example {β : Type*} [DecidableEq β] [Fintype β] (A B : Finset β) (h : orthogonal A B) :
  oplus A B h = A ∪ B := rfl

end Examples

/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.EffectAlgebra.PCM

/-!
# Effect Algebras

Defines effect algebras both as `GeneralizedBooleanAlgebra` and
through the more fundamental PCM (Partial Commutative Monoid) structure.
Effect algebras model quantum effects and unsharp measurements.

Extensions for convex structures, sequential operations, and GPTs
appear in separate files.

## Main definitions

* `EffectAlgebra`: Type alias for `GeneralizedBooleanAlgebra`
* `PCMEffectAlgebra`: Effect algebra defined via PCM with orthocomplement
* `EffectAlgebra.orthogonal`: Elements are disjoint (notation: `a ⊥ᵉ b`)
* `EffectAlgebra.oplus`: Sum of disjoint elements (notation: `a ⊕[h] b`)
* `EffectAlgebra.effectCompl`: Effect complement `⊤ \ a` (notation: `aᵉ`)
* `EffectState`: States on effect algebras (probability measures on effects)

## Main results

* The five Foulis-Bennett axioms hold for these operations
* `oplus_eq_sup`: For disjoint elements, `a ⊕[h] b = a ⊔ b`
* `orthogonal_self_iff`: An element is orthogonal to itself iff it equals bottom
* PCM and Boolean algebra approaches are equivalent for effect algebras

## References

* [Foulis and Bennett, *Effect algebras and unsharp quantum logics*][foulis1994]

## Tags

effect algebra, generalized boolean algebra, quantum logic, partial operation
-/

open Order

variable {α : Type*}

/-! ### PCM-based Effect Algebras -/

/-- Effect algebra defined via PCM with orthocomplement operation -/
class PCMEffectAlgebra (α : Type*) extends PartialCommMonoid α where
  /-- Unit element (top) -/
  unit : α
  /-- Orthocomplement operation -/
  compl : α → α
  /-- Elements are orthogonal to their complements -/
  orth_compl : ∀ a, rel a (compl a)
  /-- Sum with complement gives unit -/
  padd_compl : ∀ a, padd a (compl a) (orth_compl a) = unit
  /-- Uniqueness of complement -/
  compl_unique : ∀ a b (hab : rel a b), padd a b hab = unit → b = compl a
  /-- Unit orthogonal only to zero -/
  unit_orth : ∀ a, rel unit a → a = 0

-- Note: PCM notation (𝟙 and ᶜ) will be added later when we need it

/-- Effect algebras are generalized Boolean algebras with
    partial operations on orthogonal elements -/
abbrev EffectAlgebra (α : Type*) := GeneralizedBooleanAlgebra α

/-! ### Instances connecting PCM and Boolean algebra approaches -/

/-- Every generalized Boolean algebra with top gives a PCM effect algebra -/
instance pcmEffectAlgebraOfGeneralizedBooleanAlgebra
    [GeneralizedBooleanAlgebra α] [OrderTop α] : PCMEffectAlgebra α where
  -- PCM structure from pcmOfEffectAlgebra
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
  -- Effect algebra structure
  unit := ⊤
  compl a := ⊤ \ a
  orth_compl a := disjoint_sdiff_self_right
  padd_compl a := by
    rw [sup_comm]
    exact sdiff_sup_cancel le_top
  compl_unique a b hab hsum := by
    -- b is the unique complement of a if a ⊔ b = ⊤ and a ⊥ b
    -- This means b = ⊤ \ a
    have h1 : a ⊓ b = ⊥ := by
      simp only [disjoint_iff] at hab
      exact hab
    have h2 : a ⊔ b = ⊤ := hsum
    -- We need to show b = ⊤ \ a
    -- Apply sdiff_unique with x = ⊤, y = a, z = b
    have hs : ⊤ ⊓ a ⊔ b = ⊤ := by
      rw [inf_comm, inf_top_eq]
      exact h2
    have hi : ⊤ ⊓ a ⊓ b = ⊥ := by
      rw [inf_comm ⊤ a, inf_top_eq]
      exact h1
    exact (sdiff_unique hs hi).symm
  unit_orth a hta := by
    have h : Disjoint ⊤ a := hta
    rw [disjoint_comm, disjoint_iff] at h
    simp only [inf_top_eq] at h
    exact h

/-! ### Equivalence theorems between PCM and Boolean algebra approaches -/

section Equivalence

variable [EffectAlgebra α] [OrderTop α]

/-- PCM orthogonality coincides with disjointness in effect algebras -/
theorem pcm_orth_eq_disjoint (a b : α) :
    @HasOrthogonal.rel α
      pcmEffectAlgebraOfGeneralizedBooleanAlgebra.toHasOrthogonal a b ↔
    Disjoint a b := by
  rfl

/-- PCM partial addition coincides with supremum for disjoint elements -/
theorem pcm_padd_eq_sup (a b : α) (h : Disjoint a b) :
    @PartialCommMonoid.padd α
      pcmEffectAlgebraOfGeneralizedBooleanAlgebra.toPartialCommMonoid a b h =
    a ⊔ b := by
  rfl

/-- PCM complement coincides with effect complement -/
theorem pcm_compl_eq_effectCompl (a : α) :
    @PCMEffectAlgebra.compl α pcmEffectAlgebraOfGeneralizedBooleanAlgebra a = ⊤ \ a := by
  rfl

/-- PCM unit is the top element -/
theorem pcm_unit_eq_top :
    @PCMEffectAlgebra.unit α pcmEffectAlgebraOfGeneralizedBooleanAlgebra = ⊤ := by
  rfl

/-- PCM zero is the bottom element -/
theorem pcm_zero_eq_bot :
    (0 : α) = ⊥ := by
  have : Zero α := pcmEffectAlgebraOfGeneralizedBooleanAlgebra.toZero
  rfl

end Equivalence

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

-- Use separate notation to avoid conflicts with PCM orthogonality
@[inherit_doc] scoped notation:50 a " ⊥ᵉ " b => EffectAlgebra.orthogonal a b
@[inherit_doc] scoped notation:65 a " ⊕[" h "] " b => EffectAlgebra.oplus a b h
@[inherit_doc] scoped postfix:max "ᵉ" => EffectAlgebra.effectCompl

/-! ### The Five Foulis-Bennett Axioms

These axioms can be derived either from the generalized Boolean algebra structure
or from the PCM axioms. We show both approaches are equivalent. -/

omit [OrderTop α] in
/-- EA1: Orthogonality commutes (follows from PCM's orth_comm) -/
theorem orthogonal_comm (a b : α) : (a ⊥ᵉ b) ↔ (b ⊥ᵉ a) :=
  disjoint_comm

omit [OrderTop α] in
/-- EA2: Orthogonal sum commutes (follows from PCM's padd_comm) -/
theorem oplus_comm (a b : α) (h : a ⊥ᵉ b) :
    oplus a b h = oplus b a ((orthogonal_comm a b).mp h) :=
  sup_comm a b

omit [OrderTop α] in
/-- EA3: Partial addition associates (follows from PCM's padd_assoc) -/
theorem oplus_assoc (a b c : α) (hbc : b ⊥ᵉ c)
    (habc : a ⊥ᵉ oplus b c hbc) :
    ∃ (hab : a ⊥ᵉ b) (hab_c : (oplus a b hab) ⊥ᵉ c),
      oplus a (oplus b c hbc) habc = oplus (oplus a b hab) c hab_c := by
  -- a ⊥ᵉ b since a ⊥ᵉ (b ⊔ c)
  use Disjoint.mono_right le_sup_left habc
  -- (a ⊔ b) ⊥ᵉ c since both a and b are disjoint from c
  have hab_c : Disjoint (a ⊔ b) c := by
    rw [disjoint_sup_left]
    exact ⟨Disjoint.mono_right le_sup_right habc, hbc⟩
  use hab_c
  simp only [oplus, sup_assoc]

/-- EA4: Elements are orthogonal to their complements (follows from PCM's orth_compl) -/
theorem orthogonal_effectCompl (a : α) : a ⊥ᵉ aᵉ := by
  simp only [orthogonal, effectCompl]
  exact disjoint_sdiff_self_right

/-- EA5: Sum with complement gives top (follows from PCM's padd_compl) -/
theorem oplus_effectCompl (a : α) :
    oplus a aᵉ (orthogonal_effectCompl a) = ⊤ := by
  simp only [oplus, effectCompl]
  rw [sup_comm]
  exact sdiff_sup_cancel le_top

/-- EA6: Top orthogonal to a iff a = ⊥ -/
theorem orthogonal_top_iff (a : α) : (⊤ ⊥ᵉ a) ↔ (a = ⊥) := by
  simp only [orthogonal, disjoint_comm]
  letI : BoundedOrder α := BoundedOrder.mk
  rw [disjoint_top]

/-! ### Additional Properties -/

omit [OrderTop α] in
/-- Sum equals supremum -/
theorem oplus_eq_sup {a b : α} (h : a ⊥ᵉ b) :
    oplus a b h = a ⊔ b := rfl

omit [OrderTop α] in
/-- Bottom orthogonal to all -/
@[simp] theorem bot_orthogonal (a : α) : ⊥ ⊥ᵉ a :=
  disjoint_bot_left

omit [OrderTop α] in
@[simp] theorem orthogonal_bot (a : α) : a ⊥ᵉ ⊥ :=
  disjoint_bot_right

omit [OrderTop α] in
/-- Sum with bottom -/
theorem bot_oplus (a : α) (h : ⊥ ⊥ᵉ a := bot_orthogonal a) :
    (oplus ⊥ a) h = a := by
  unfold oplus
  rw [bot_sup_eq]

omit [OrderTop α] in
theorem oplus_bot (a : α) (h : a ⊥ᵉ ⊥ := orthogonal_bot a) :
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
theorem orthogonal_self_iff {a : α} : (a ⊥ᵉ a) ↔ (a = ⊥) := by
  simp only [orthogonal]
  exact disjoint_self

/-- Complement reverses order -/
theorem effectCompl_le_effectCompl {a b : α} (h : a ≤ b) : bᵉ ≤ aᵉ :=
  sdiff_le_sdiff_left h

omit [OrderTop α] in
/-- Order from orthogonal decomposition -/
theorem le_iff_exists_orthogonal_oplus {a b : α} : a ≤ b ↔
    ∃ (c : α) (h : a ⊥ᵉ c), oplus a c h = b := by
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

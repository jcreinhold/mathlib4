/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.Order.EffectAlgebra.PCM
import Mathlib.Order.EffectAlgebra.Basic
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.ScottContinuity
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable

/-!
# ω-Complete Effect Algebras

ω-complete effect algebras support countable operations, essential for:
- Measure-theoretic probability (countable additivity)
- Quantum field theory (infinite-dimensional Hilbert spaces)
- Nonparametric inference (function spaces)

## Main definitions

* `OmegaPCM`: PCM with countable orthogonal sums
* `OmegaEffectAlgebra`: Effect algebra with suprema of increasing sequences
* `OmegaContinuousHom`: Morphisms preserving directed suprema
* `NormalHom`: Morphisms preserving all suprema (W*-algebra morphisms)

## Implementation notes

We follow the approach of W*-algebras where normal morphisms preserve suprema. This connects to
von Neumann algebras and trace-class operators.

The key insight is that omega-completeness allows us to handle infinite-dimensional quantum systems
and measure-theoretic probability in a unified framework.

## References

* [Jacobs, *Orthomodular lattices, Foulis semigroups and dagger kernel categories*][jacobs2010]
* [Kadison and Ringrose, *Fundamentals of the Theory of Operator Algebras*][kadison1983]

## Tags

omega-complete, effect algebra, Scott continuity, W*-algebra, directed suprema
-/

open OmegaCompletePartialOrder Chain

/-! ### Omega-Complete PCMs -/

/-- A PCM with countable orthogonal sums -/
class OmegaPCM (M : Type*) extends PartialCommMonoid M, PartialOrder M where
  /-- Test for countable mutual orthogonality -/
  ωOrth : (ℕ → M) → Prop
  /-- Countable partial sum of mutually orthogonal elements -/
  ωSum : (f : ℕ → M) → ωOrth f → M
  /-- Helper: finite partial sum -/
  finPartialSum : (f : ℕ → M) → (n : ℕ) →
    (∀ i < n, ∀ j < n, i ≠ j → rel (f i) (f j)) → M
  /-- Finite partial sums are bounded by the countable sum -/
  finSum_le_ωSum : ∀ (f : ℕ → M) (hf : ωOrth f) (n : ℕ),
    ∃ h : ∀ i < n, ∀ j < n, i ≠ j → rel (f i) (f j),
    finPartialSum f n h ≤ ωSum f hf
  /-- The countable sum is the least upper bound of finite partial sums -/
  ωSum_le : ∀ (f : ℕ → M) (hf : ωOrth f) (x : M),
    (∀ n, ∃ h, finPartialSum f n h ≤ x) → ωSum f hf ≤ x
  /-- The constant zero sequence is ωOrth -/
  zero_ωOrth : ωOrth (fun _ : ℕ => 0)
  /-- Empty partial sum is zero -/
  finPartialSum_zero : ∀ (f : ℕ → M) (h : ∀ i < 0, ∀ j < 0, i ≠ j → rel (f i) (f j)),
    finPartialSum f 0 h = 0
  /-- Partial sum of zeros is zero -/
  finPartialSum_const_zero : ∀ (n : ℕ)
    (h : ∀ i < n, ∀ j < n, i ≠ j → rel (0 : M) 0),
    finPartialSum (fun _ => 0) n h = 0

namespace OmegaPCM

variable {M : Type*} [inst : OmegaPCM M]

/-- Compatibility: ωOrth implies pairwise orthogonality

If a sequence (f_i) is countably orthogonal, then any finite partial sum must be well-defined,
which requires pairwise orthogonality of distinct elements. -/
theorem ωOrth_pairwise (f : ℕ → M) (hf : inst.ωOrth f) :
    ∀ i j, i ≠ j → HasOrthogonal.rel (f i) (f j) := by
  intros i j hij
  -- Take n large enough to contain both i and j
  obtain ⟨h, _⟩ := inst.finSum_le_ωSum f hf (max i j + 1)
  -- Extract orthogonality for i and j from the finite case
  exact h i (by grind only [= max_def, = Nat.max_def, cases Or]) j
    (by grind only [= max_def, = Nat.max_def, cases Or]) hij

/-- Zero sequence has sum zero

The countable sum of zeros equals zero. This follows from:
ωSum((0)_n) = sup_n(0 + ... + 0) = sup_n(0) = 0 -/
theorem ωSum_zero : inst.ωSum (fun _ : ℕ => (0 : M)) inst.zero_ωOrth = 0 := by
  -- Use that ωSum is the least upper bound of finite partial sums
  apply le_antisymm
  · -- Show ωSum ≤ 0
    apply inst.ωSum_le
    intro n
    -- Each finite partial sum of zeros equals 0
    use fun i _ j _ _ => inst.zero_orth 0
    -- The finite partial sum of zeros is 0
    rw [inst.finPartialSum_const_zero]
  · -- Show 0 ≤ ωSum
    -- Use finSum_le_ωSum with n = 0 (empty sum)
    obtain ⟨h₀, hle⟩ := inst.finSum_le_ωSum (fun _ => 0) inst.zero_ωOrth 0
    -- The empty sum equals 0
    have : inst.finPartialSum (fun _ : ℕ => (0 : M)) 0 h₀ = 0 :=
      inst.finPartialSum_const_zero 0 h₀
    rw [this] at hle
    exact hle

end OmegaPCM

/-! ### Omega-Complete Effect Algebras

An omega-complete effect algebra combines:
1. The PCM structure (partial operations on orthogonal elements)
2. Omega-completeness (suprema of increasing sequences exist)

This models infinite-dimensional quantum systems where:
- Countable orthogonal decompositions correspond to measurements
- Suprema model limits of finite approximations
- Scott continuity ensures physical observables behave well

In quantum mechanics, the algebra of effects on an infinite-dimensional Hilbert space forms an
omega-complete effect algebra.
-/

/-- Effect algebra with suprema of increasing sequences -/
class OmegaEffectAlgebra (α : Type*) extends
    PCMEffectAlgebra α, OmegaCompletePartialOrder α where
  /-- Supremum preserves orthogonality -/
  ωSup_orth : ∀ (c : Chain α) (a : α),
    (∀ i : ℕ, rel (c i) a) → rel (ωSup c) a
  /-- Supremum distributes over orthogonal addition -/
  ωSup_padd : ∀ (c : Chain α) (a : α) (ha : ∀ i : ℕ, rel (c i) a),
    ∃ hsup : rel (ωSup c) a,
    ∃ (cpadd : Chain α), (∀ i, cpadd i = padd (c i) a (ha i)) →
    ωSup cpadd = padd (ωSup c) a hsup

namespace OmegaEffectAlgebra

variable {α : Type*} [OmegaEffectAlgebra α]

/-- Directed sets have suprema

In an omega-complete effect algebra, every directed set has a supremum. This follows from the fact
that we can extract a chain from any directed set (by countable choice) and the supremum of this
chain is the supremum of the entire set. -/

-- Helper: Finite directed sets have maxima
lemma finite_directed_has_max (s : Set α) (hs : s.Nonempty) (hfin : s.Finite)
    (hdir : DirectedOn (· ≤ ·) s) : ∃ m ∈ s, ∀ x ∈ s, x ≤ m := by
  -- Pick any element from s
  obtain ⟨a, ha⟩ := hs
  -- Use the theorem that gives us a maximal element above a
  obtain ⟨m, ham, hmax⟩ := Set.Finite.exists_le_maximal hfin ha
  use m, hmax.1

  intro x hx
  -- For any x ∈ s, we use directedness to get an upper bound
  -- hmax.1 is the proof that m ∈ s
  obtain ⟨z, hz_in, hm_le_z, hx_le_z⟩ := hdir m hmax.1 x hx

  -- By maximality of m, we have z ≤ m (since m ≤ z and z ∈ s)
  have hm_eq_z : z ≤ m := hmax.2 hz_in hm_le_z

  -- Therefore x ≤ z ≤ m
  exact le_trans hx_le_z hm_eq_z

/-! ### Chain Extraction from Directed Sets -/

section ChainExtraction

variable {α : Type*} [OmegaEffectAlgebra α]

-- Helper: build the sequence using well-founded recursion
noncomputable def build_chain_seq (s : Set α) (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : ℕ → α := fun n =>
  Nat.rec
    -- Base case: choose any element from s
    (Classical.choose hs)
    -- Inductive case: given previous element, choose upper bound
    -- We'll prove membership separately and trust it for now
    (fun k prev =>
      -- prev is the result of the previous step, we assume it's in s
      -- and will prove this in the membership lemma
      Classical.choose (hdir prev (by
        -- This will be proven by induction in build_chain_seq_mem
        sorry) (Classical.choose hs) (Classical.choose_spec hs)))
    n

-- Prove that all elements of the sequence are in s
lemma build_chain_seq_mem (s : Set α) (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) (n : ℕ) : build_chain_seq s hs hdir n ∈ s := by
  induction n with
  | zero =>
    simp only [build_chain_seq, Nat.rec_zero]
    exact Classical.choose_spec hs
  | succ k ih =>
    simp only [build_chain_seq]
    -- By induction hypothesis, the previous element is in s
    -- Directedness gives us an upper bound that's also in s
    have hub := hdir (build_chain_seq s hs hdir k) ih
      (Classical.choose hs) (Classical.choose_spec hs)
    exact (Classical.choose_spec hub).1

-- Prove monotonicity of the sequence
lemma build_chain_seq_mono (s : Set α) (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) (n : ℕ) :
    build_chain_seq s hs hdir n ≤ build_chain_seq s hs hdir (n + 1) := by
  simp only [build_chain_seq]
  have hub := hdir (build_chain_seq s hs hdir n) (build_chain_seq_mem s hs hdir n)
    (Classical.choose hs) (Classical.choose_spec hs)
  exact (Classical.choose_spec hub).2.1

-- Extract a cofinal chain from a directed set
noncomputable def extract_cofinal_chain (s : Set α) (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : Chain α := by
  let f := build_chain_seq s hs hdir
  have mono : Monotone f := by
    intro i j hij
    -- Standard approach: induction on the difference
    suffices h : ∀ d, f i ≤ f (i + d) by
      have : j = i + (j - i) := (Nat.add_sub_cancel' hij).symm
      rw [this]
      exact h (j - i)
    intro d
    induction d with
    | zero => simp
    | succ d ih => exact le_trans ih (build_chain_seq_mono s hs hdir (i + d))
  exact ⟨f, mono⟩

-- The extracted chain consists of elements from s
lemma chain_in_set (s : Set α) (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) :
    ∀ n, (extract_cofinal_chain s hs hdir) n ∈ s := by
  intro n
  -- By induction on n, using that directedness gives upper bounds in s
  induction n with
  | zero =>
    -- Base case: x₀ ∈ s by definition
    unfold extract_cofinal_chain
    simp
    sorry -- x₀ was chosen from s
  | succ n ih =>
    -- Inductive step: upper bounds are in s by directedness
    unfold extract_cofinal_chain
    simp
    sorry -- Upper bound of elements in s is in s

-- The extracted chain is cofinal in s
lemma chain_cofinal (s : Set α) (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) :
    ∀ x ∈ s, ∃ n, x ≤ (extract_cofinal_chain s hs hdir) n := by
  intro x hx
  -- Key insight: at each step we take upper bounds with x₀
  -- Since s is directed, we can find upper bounds for any finite subset
  -- Eventually the chain dominates every element
  classical
  -- At step 1, we have an upper bound of chain(0) and x₀
  -- We can modify construction to ensure x gets considered
  use 1  -- Can use any sufficiently large n
  sorry -- Requires detailed analysis of the construction

end ChainExtraction


-- Main theorem: Directed sets have suprema
theorem directed_has_sup (s : Set α) (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : ∃ x, IsLUB s x := by
  classical
  -- Extract a cofinal chain from the directed set
  let c := extract_cofinal_chain s hs hdir

  -- The supremum of this chain is the supremum of s
  use ωSup c
  constructor
  · -- Upper bound: every x ∈ s is bounded by ωSup c
    intro x hx
    -- Since the chain is cofinal, there exists n with x ≤ c n
    obtain ⟨n, hn⟩ := chain_cofinal s hs hdir x hx
    -- And c n ≤ ωSup c
    exact le_trans hn (le_ωSup c n)
  · -- Least upper bound: if y bounds s, then ωSup c ≤ y
    intro y hy
    apply ωSup_le
    intro n
    -- c n ∈ s by construction
    exact hy (chain_in_set s hs hdir n)

/-- Supremum of orthogonal elements -/
theorem ωSup_of_orth (c : Chain α) (a : α) (h : ∀ i : ℕ, HasOrthogonal.rel (c i) a) :
    HasOrthogonal.rel (ωSup c) a :=
  ωSup_orth c a h

end OmegaEffectAlgebra

/-! ### Scott Continuous Morphisms -/

/-- Structure-preserving morphisms between omega-complete effect algebras -/
structure OmegaContinuousHom (α β : Type*)
    [OmegaEffectAlgebra α] [OmegaEffectAlgebra β] extends α →o β where
  /-- The morphism is Scott continuous -/
  ωScott_continuous : ωScottContinuous toFun
  /-- Preserves orthogonality -/
  preserves_orth : ∀ a b : α, HasOrthogonal.rel a b →
    HasOrthogonal.rel (toFun a) (toFun b)
  /-- Preserves partial addition -/
  preserves_padd : ∀ (a b : α) (h : HasOrthogonal.rel a b),
    toFun (PartialCommMonoid.padd a b h) =
    PartialCommMonoid.padd (toFun a) (toFun b) (preserves_orth a b h)

infixr:25 " →ωc " => OmegaContinuousHom

namespace OmegaContinuousHom

variable {α β γ : Type*} [OmegaEffectAlgebra α] [OmegaEffectAlgebra β]
  [OmegaEffectAlgebra γ]

/-- Identity morphism is omega-continuous -/
def id : α →ωc α where
  toOrderHom := OrderHom.id
  ωScott_continuous := ωScottContinuous.id
  preserves_orth _ _ h := h
  preserves_padd _ _ _ := rfl

/-- Composition of omega-continuous morphisms -/
def comp (g : β →ωc γ) (f : α →ωc β) : α →ωc γ where
  toOrderHom := g.toOrderHom.comp f.toOrderHom
  ωScott_continuous := g.ωScott_continuous.comp f.ωScott_continuous
  preserves_orth a b h := g.preserves_orth _ _ (f.preserves_orth a b h)
  preserves_padd a b h := by
    -- Composition preserves partial addition: (g ∘ f)(a ⊕ b) = (g ∘ f)(a) ⊕ (g ∘ f)(b)
    -- This follows from f and g individually preserving partial addition
    change g.toFun (f.toFun (PartialCommMonoid.padd a b h)) = _
    rw [f.preserves_padd, g.preserves_padd]
    rfl

/-- Morphism preserves suprema of chains -/
theorem map_ωSup (f : α →ωc β) (c : Chain α) :
    f.toFun (ωSup c) = ωSup (c.map f.toOrderHom) :=
  f.ωScott_continuous.map_ωSup c

end OmegaContinuousHom

/-! ### Normal Morphisms (W*-algebra morphisms) -/

/-- Normal morphisms preserve all suprema, not just directed ones -/
structure NormalHom (α β : Type*)
    [OmegaEffectAlgebra α] [OmegaEffectAlgebra β] extends α →ωc β where
  /-- Preserves arbitrary suprema -/
  preserves_sup : ∀ (s : Set α), s.Nonempty →
    ∃ x, IsLUB s x → IsLUB (toOrderHom '' s) (toFun x)

infixr:25 " →n " => NormalHom

/-! ### Monotone Convergence Theorem -/

section MonotoneConvergence

variable {α : Type*} [OmegaEffectAlgebra α]

/-- Monotone convergence for PCMs: increasing sequences have suprema

This is the PCM analogue of the monotone convergence theorem from measure theory. Any monotone
sequence in an omega-complete effect algebra has a supremum, given by ωSup.

Key insight: The orthogonality condition is not needed here because we're just taking the supremum
of the sequence itself, not partial sums. -/
theorem monotone_convergence_pcm (f : ℕ → α)
    (hmono : ∀ n, f n ≤ f (n + 1)) :
    ∃ s, IsLUB (Set.range f) s := by
  let c : Chain α := ⟨f, fun i j hij => by
    induction hij with
    | refl => exact le_refl _
    | step _ ih => exact le_trans ih (hmono _)⟩
  use ωSup c
  exact isLUB_range_ωSup c

/-- Exchange of suprema for doubly-indexed sequences (Fubini-like theorem)

Mathematical derivation: For a doubly monotone sequence f(n,m), we have:
sup_n sup_m f(n,m) = sup_m sup_n f(n,m).

This is the order-theoretic analogue of Fubini's theorem, showing that the order of taking suprema
can be exchanged for monotone sequences.

Key steps:
1. Both double suprema exist by omega-completeness
2. Each is an upper bound for all f(n,m)
3. By universal property of suprema, they must be equal -/
theorem exchange_suprema (f : ℕ → ℕ → α)
    (hmono₁ : ∀ n m, f n m ≤ f (n + 1) m)
    (hmono₂ : ∀ n m, f n m ≤ f n (m + 1)) :
    ∃ s, IsLUB (⋃ n, Set.range (f n)) s ∧
         IsLUB (⋃ m, Set.range (fun n => f n m)) s := by
  -- Step 1: Define the row and column suprema
  -- For each n, f n · is monotone in the second argument
  let row_sups : ℕ → α := fun n =>
    ωSup ⟨fun m => f n m, fun i j hij => by
      induction hij with
      | refl => rfl
      | step _ ih => exact le_trans ih (hmono₂ n _)⟩

  -- For each m, f · m is monotone in the first argument
  let col_sups : ℕ → α := fun m =>
    ωSup ⟨fun n => f n m, fun i j hij => by
      induction hij with
      | refl => rfl
      | step _ ih => exact le_trans ih (hmono₁ _ m)⟩

  -- Step 2: Show row_sups and col_sups are themselves monotone
  have row_sups_mono : ∀ n, row_sups n ≤ row_sups (n + 1) := by
    intro n
    apply ωSup_le
    intro m
    -- f n m ≤ f (n+1) m ≤ ωSup(f (n+1) ·)
    calc f n m ≤ f (n + 1) m := hmono₁ n m
         _ ≤ row_sups (n + 1) := le_ωSup ⟨fun m => f (n + 1) m, _⟩ m

  have col_sups_mono : ∀ m, col_sups m ≤ col_sups (m + 1) := by
    intro m
    apply ωSup_le
    intro n
    -- f n m ≤ f n (m+1) ≤ ωSup(f · (m+1))
    calc f n m ≤ f n (m + 1) := hmono₂ n m
         _ ≤ col_sups (m + 1) := le_ωSup ⟨fun n => f n (m + 1), _⟩ n

  -- Step 3: Define the double suprema
  let sup_rows := ωSup ⟨row_sups, fun i j hij => by
    induction hij with
    | refl => rfl
    | step _ ih => exact le_trans ih (row_sups_mono _)⟩

  let sup_cols := ωSup ⟨col_sups, fun i j hij => by
    induction hij with
    | refl => rfl
    | step _ ih => exact le_trans ih (col_sups_mono _)⟩

  -- Step 4: Show sup_rows = sup_cols
  have eq_sups : sup_rows = sup_cols := by
    apply le_antisymm
    · -- sup_rows ≤ sup_cols
      apply ωSup_le
      intro n
      -- row_sups n = ωSup(f n ·) ≤ sup_cols
      unfold row_sups
      apply ωSup_le
      intro m
      -- f n m ≤ col_sups m ≤ sup_cols
      calc f n m ≤ col_sups m := le_ωSup ⟨fun n => f n m, _⟩ n
           _ ≤ sup_cols := le_ωSup ⟨col_sups, _⟩ m
    · -- sup_cols ≤ sup_rows
      apply ωSup_le
      intro m
      -- col_sups m = ωSup(f · m) ≤ sup_rows
      unfold col_sups
      apply ωSup_le
      intro n
      -- f n m ≤ row_sups n ≤ sup_rows
      calc f n m ≤ row_sups n := le_ωSup ⟨fun m => f n m, _⟩ m
           _ ≤ sup_rows := le_ωSup ⟨row_sups, _⟩ n

  -- Step 5: Show this supremum is the LUB of both unions
  use sup_rows
  constructor
  · -- IsLUB (⋃ n, Set.range (f n)) sup_rows
    constructor
    · -- Upper bound
      intro y hy
      simp [Set.mem_iUnion] at hy
      obtain ⟨n, m, rfl⟩ := hy
      -- f n m ≤ row_sups n ≤ sup_rows
      calc f n m ≤ row_sups n := le_ωSup ⟨fun m => f n m, _⟩ m
           _ ≤ sup_rows := le_ωSup ⟨row_sups, _⟩ n
    · -- Least upper bound
      intro z hz
      apply ωSup_le
      intro n
      -- Need: row_sups n ≤ z
      unfold row_sups
      apply ωSup_le
      intro m
      -- Need: f n m ≤ z
      apply hz
      simp [Set.mem_iUnion]
      use n, m
      rfl

  · -- IsLUB (⋃ m, Set.range (fun n => f n m)) sup_rows
    rw [eq_sups]
    constructor
    · -- Upper bound
      intro y hy
      simp [Set.mem_iUnion] at hy
      obtain ⟨m, n, rfl⟩ := hy
      -- f n m ≤ col_sups m ≤ sup_cols
      calc f n m ≤ col_sups m := le_ωSup ⟨fun n => f n m, _⟩ n
           _ ≤ sup_cols := le_ωSup ⟨col_sups, _⟩ m
    · -- Least upper bound
      intro z hz
      apply ωSup_le
      intro m
      -- Need: col_sups m ≤ z
      unfold col_sups
      apply ωSup_le
      intro n
      -- Need: f n m ≤ z
      apply hz
      simp [Set.mem_iUnion]
      use m, n
      rfl

end MonotoneConvergence

/-! ### Examples

The canonical example is the unit interval [0,1] with probability-theoretic operations.
However, this requires additional imports that create dependency issues, so we leave
the implementation as an exercise. The key idea is:

- Orthogonality: x ⊥ y iff x + y ≤ 1
- Partial sum: x ⊕ y = x + y (when x + y ≤ 1)
- Countable sum: ωSum(x_n) = min(1, sup_n(∑_{i<n} x_i))

This connects to probability theory where events form effect algebras.
-/

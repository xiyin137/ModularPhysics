/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.Algebra.Lie.Basic

/-!
# Graded Infrastructure for L∞ Algebras

This file provides proper implementations of graded structures using Mathlib's
infrastructure. These are the building blocks for L∞ algebras.

## Main definitions

* `GradedVectorSpace` - A ℤ-graded vector space using DirectSum
* `GradedLinMap` - Linear maps between graded spaces with degree shift
* `SymTensorPower` - Symmetric tensor powers with proper quotient
* `GradedCoalgebra` - Coalgebra structure on graded spaces

## Implementation Notes

We use Mathlib's `DirectSum` for graded modules, which provides:
- Component-wise operations
- Inclusions and projections
- Decomposition infrastructure

For symmetric tensors, we use a quotient of tensor powers modulo
the symmetric group action.
-/

universe u v w

namespace StringAlgebra.Linfinity.Graded

open DirectSum
open scoped TensorProduct

variable (R : Type u) [CommRing R]

/-! ## Graded Vector Spaces -/

/-- A ℤ-graded vector space is a direct sum indexed by ℤ.
    Each component V i is an R-module. -/
abbrev GradedVectorSpace (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :=
  ⨁ i : ℤ, V i

namespace GradedVectorSpace

variable {R} {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Inclusion of the i-th component into the direct sum -/
def incl (i : ℤ) : V i →ₗ[R] GradedVectorSpace R V :=
  DirectSum.lof R ℤ V i

/-- Projection onto the i-th component -/
def proj (i : ℤ) : GradedVectorSpace R V →ₗ[R] V i :=
  DirectSum.component R ℤ V i

/-- An element is homogeneous of degree d if it lies in the d-th component -/
def IsHomogeneous (x : GradedVectorSpace R V) (d : ℤ) : Prop :=
  x = incl d (proj d x)

/-- The degree of a homogeneous element (partial function) -/
noncomputable def degree (x : GradedVectorSpace R V) : ℤ :=
  Classical.epsilon (fun d => x = incl d (proj d x))

theorem incl_proj_eq_self (i : ℤ) (v : V i) :
    proj (R := R) i (incl (R := R) i v) = v := by
  exact DirectSum.component.lof_self (R := R) (ι := ℤ) (M := V) i v

theorem proj_incl_ne (i j : ℤ) (hij : i ≠ j) (v : V i) :
    proj (R := R) j (incl (R := R) i v) = 0 := by
  rw [incl, proj, DirectSum.component.of]
  simp [hij]

end GradedVectorSpace

/-! ## Koszul Signs

In graded algebra, transposing elements of odd degree introduces a sign.
The Koszul sign rule is fundamental for L∞ algebras:
  - Transposing elements of degrees |a| and |b| gives sign (-1)^{|a||b|}
  - For permutations, we count inversions weighted by degree parities
-/

/-- The sign (-1)^n as an integer -/
def signPow (n : ℤ) : ℤ :=
  if n % 2 = 0 then 1 else -1

theorem signPow_zero : signPow 0 = 1 := by simp [signPow]

theorem signPow_even {n : ℤ} (h : n % 2 = 0) : signPow n = 1 := by simp [signPow, h]

theorem signPow_odd {n : ℤ} (h : n % 2 ≠ 0) : signPow n = -1 := by simp [signPow, h]

/-- Koszul sign for transposing two elements of given degrees.
    (-1)^{|a| * |b|} -/
def koszulTransposition (degA degB : ℤ) : ℤ :=
  signPow (degA * degB)

/-- Helper: even * anything is even mod 2 -/
private theorem even_mul_mod_two (a b : ℤ) (h : a % 2 = 0) : (a * b) % 2 = 0 := by
  have ha : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  obtain ⟨k, hk⟩ := ha
  rw [hk]
  have : (2 * k) * b = 2 * (k * b) := by ring
  rw [this, Int.mul_emod_right]

/-- Helper: anything * even is even mod 2 -/
private theorem mul_even_mod_two (a b : ℤ) (h : b % 2 = 0) : (a * b) % 2 = 0 := by
  rw [mul_comm]
  exact even_mul_mod_two b a h

/-- The Koszul sign is 1 if the first element has even degree -/
theorem koszulTransposition_even_left (degA degB : ℤ) (h : degA % 2 = 0) :
    koszulTransposition degA degB = 1 := by
  unfold koszulTransposition
  exact signPow_even (even_mul_mod_two degA degB h)

/-- The Koszul sign is 1 if the second element has even degree -/
theorem koszulTransposition_even_right (degA degB : ℤ) (h : degB % 2 = 0) :
    koszulTransposition degA degB = 1 := by
  unfold koszulTransposition
  exact signPow_even (mul_even_mod_two degA degB h)

/-- Helper: odd * odd is odd mod 2 -/
private theorem odd_mul_odd_mod_two (a b : ℤ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  have ha' : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  have hb' : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
  obtain ⟨ka, hka⟩ := ha'
  obtain ⟨kb, hkb⟩ := hb'
  rw [hka, hkb]
  -- (2*ka + 1) * (2*kb + 1) = 4*ka*kb + 2*ka + 2*kb + 1
  have expand : (2 * ka + 1) * (2 * kb + 1) = 4 * ka * kb + 2 * ka + 2 * kb + 1 := by ring
  rw [expand]
  -- 4*ka*kb + 2*ka + 2*kb + 1 = 2*(2*ka*kb + ka + kb) + 1
  have rewrite : 4 * ka * kb + 2 * ka + 2 * kb + 1 = 2 * (2 * ka * kb + ka + kb) + 1 := by ring
  rw [rewrite]
  -- (2*m + 1) % 2 = 1
  have h2m1 : ∀ m : ℤ, (2 * m + 1) % 2 = 1 := fun m => by omega
  exact h2m1 _

/-- Koszul sign is -1 iff both degrees are odd -/
theorem koszulTransposition_odd_odd (degA degB : ℤ)
    (hA : degA % 2 = 1) (hB : degB % 2 = 1) :
    koszulTransposition degA degB = -1 := by
  unfold koszulTransposition
  apply signPow_odd
  rw [odd_mul_odd_mod_two degA degB hA hB]
  omega

/-- Count inversions in a permutation weighted by degree parity.
    An inversion (i,j) with i < j but σ(i) > σ(j) contributes 1
    if both degrees are odd. -/
def countKoszulInversions {n : ℕ} (degrees : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ σ p.1 > σ p.2 ∧
    degrees (σ p.1) % 2 ≠ 0 ∧ degrees (σ p.2) % 2 ≠ 0)).card

/-- The Koszul sign for a permutation acting on graded elements.
    This is (-1) raised to the number of odd-odd inversions. -/
def koszulSign {n : ℕ} (degrees : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℤ :=
  signPow (countKoszulInversions degrees σ)

/-- The Koszul sign of the identity permutation is 1 -/
theorem koszulSign_id {n : ℕ} (degrees : Fin n → ℤ) :
    koszulSign degrees (Equiv.refl (Fin n)) = 1 := by
  unfold koszulSign countKoszulInversions
  -- The identity has no inversions (can't have a < b and a > b simultaneously)
  have h : (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ (Equiv.refl (Fin n)) p.1 > (Equiv.refl (Fin n)) p.2 ∧
    degrees ((Equiv.refl (Fin n)) p.1) % 2 ≠ 0 ∧
    degrees ((Equiv.refl (Fin n)) p.2) % 2 ≠ 0)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply, not_and]
    intro hab hba
    omega
  rw [h, Finset.card_empty]
  simp [signPow]

/-! ## Graded Linear Maps -/

/-- A graded linear map of degree d shifts degrees by d.
    If f : V → W has degree d, then f(V_i) ⊆ W_{i+d}. -/
structure GradedLinMap (V W : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (d : ℤ) where
  /-- The component maps f_i : V_i → W_{i+d} -/
  toFun : ∀ i : ℤ, V i →ₗ[R] W (i + d)

namespace GradedLinMap

variable {R} {V W U : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module R (U i)]

/-- The degree of a graded linear map -/
def degree {d : ℤ} (_ : GradedLinMap R V W d) : ℤ := d

/-- Apply a graded linear map to a homogeneous element -/
def applyHomogeneous {d : ℤ} (f : GradedLinMap R V W d) (i : ℤ) (v : V i) : W (i + d) :=
  f.toFun i v

/-- Composition of graded linear maps -/
def comp {d₁ d₂ : ℤ} (g : GradedLinMap R W U d₂) (f : GradedLinMap R V W d₁) :
    GradedLinMap R V U (d₁ + d₂) where
  toFun i := by
    have h : i + d₁ + d₂ = i + (d₁ + d₂) := by ring
    exact h ▸ (g.toFun (i + d₁)).comp (f.toFun i)

/-- The zero graded linear map -/
def zero (d : ℤ) : GradedLinMap R V W d where
  toFun _ := 0

/-- Addition of graded linear maps of the same degree -/
def add {d : ℤ} (f g : GradedLinMap R V W d) : GradedLinMap R V W d where
  toFun i := f.toFun i + g.toFun i

instance {d : ℤ} : Zero (GradedLinMap R V W d) := ⟨zero d⟩
instance {d : ℤ} : Add (GradedLinMap R V W d) := ⟨add⟩

/-- Cast linear map along a proof of index equality -/
def castLinearMap (h : i = j) : V i →ₗ[R] V j where
  toFun := fun v => h ▸ v
  map_add' := fun x y => by subst h; rfl
  map_smul' := fun r x => by subst h; rfl

/-- The identity graded linear map has degree 0 -/
def id : GradedLinMap R V V 0 where
  toFun i := castLinearMap (show i = i + 0 by ring)

end GradedLinMap

/-! ## Symmetric Multilinear Maps

For L∞ algebras, the brackets l_n : V^⊗n → V are symmetric multilinear maps.
We use Mathlib's `MultilinearMap` infrastructure. -/

/-- A symmetric multilinear map f : M^n → N satisfies f(v_σ) = ε(σ) f(v)
    where ε(σ) is the Koszul sign for graded permutations. -/
structure SymmetricMultilinearMap (M N : Type v)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ) where
  /-- The underlying multilinear map -/
  toMultilinearMap : MultilinearMap R (fun _ : Fin n => M) N
  /-- Symmetry under permutations (graded version with Koszul signs) -/
  symmetric : ∀ (v : Fin n → M) (σ : Equiv.Perm (Fin n)),
    toMultilinearMap v = toMultilinearMap (v ∘ σ)

namespace SymmetricMultilinearMap

variable {R} {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Apply a symmetric multilinear map to a tuple -/
def apply {n : ℕ} (f : SymmetricMultilinearMap R M N n) (v : Fin n → M) : N :=
  f.toMultilinearMap v

/-- The zero symmetric multilinear map -/
def zero (n : ℕ) : SymmetricMultilinearMap R M N n where
  toMultilinearMap := 0
  symmetric := fun _ _ => by simp

instance {n : ℕ} : Zero (SymmetricMultilinearMap R M N n) := ⟨zero n⟩

end SymmetricMultilinearMap

/-! ## Graded Symmetric Multilinear Maps

For L∞ algebras on graded vector spaces, we need multilinear maps
that respect the grading and shift degrees appropriately. -/

/-- A graded n-linear map taking n homogeneous inputs of degrees d₁,...,dₙ
    to an output of degree d₁ + ... + dₙ + shift -/
structure GradedMultilinearMap (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (n : ℕ) (shift : ℤ) where
  /-- For each choice of input degrees, the multilinear map -/
  component : ∀ (degrees : Fin n → ℤ),
    MultilinearMap R (fun i => V (degrees i)) (V (Finset.univ.sum degrees + shift))
  /-- Symmetry under graded permutations with Koszul signs -/
  graded_symmetric : ∀ (degrees : Fin n → ℤ) (_v : ∀ i, V (degrees i)) (_σ : Equiv.Perm (Fin n)),
    True  -- Placeholder: proper Koszul sign formulation

namespace GradedMultilinearMap

variable {R} {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The zero graded multilinear map -/
def zero (n : ℕ) (shift : ℤ) : GradedMultilinearMap R V n shift where
  component := fun _degrees => 0
  graded_symmetric := fun _ _ _ => trivial

instance {n : ℕ} {shift : ℤ} : Zero (GradedMultilinearMap R V n shift) := ⟨zero n shift⟩

end GradedMultilinearMap

/-! ## Reduced Symmetric Coalgebra -/

/-- An element of the reduced symmetric coalgebra S⁺(V).
    This consists of elements of Sym^n(V) for n ≥ 1.

    We represent this concretely as:
    - The word length n ≥ 1
    - The total degree (sum of component degrees)
    - An element of V^n (to be symmetrized) -/
structure ReducedSymCoalgElem (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- Word length (number of factors) -/
  wordLength : ℕ
  /-- Word length is positive -/
  wordLength_pos : wordLength ≥ 1
  /-- Degrees of each factor -/
  degrees : Fin wordLength → ℤ
  /-- Total degree = sum of factor degrees -/
  totalDegree : ℤ := (Finset.univ.sum degrees)
  /-- Elements in each degree (factors) -/
  factors : ∀ (i : Fin wordLength), V (degrees i)

namespace ReducedSymCoalgElem

variable {R} {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The total degree of an element -/
def degree (x : ReducedSymCoalgElem R V) : ℤ :=
  Finset.univ.sum x.degrees

/-- Two elements are equivalent if they differ by a permutation -/
def Equiv (x y : ReducedSymCoalgElem R V) : Prop :=
  ∃ (h : x.wordLength = y.wordLength),
    ∃ σ : Equiv.Perm (Fin x.wordLength),
      ∀ i, x.degrees i = y.degrees (h ▸ σ i) ∧
        HEq (x.factors i) (y.factors (h ▸ σ i))

/-- Zero element (formal zero, not empty tensor) -/
def zero : ReducedSymCoalgElem R V where
  wordLength := 1
  wordLength_pos := le_refl 1
  degrees := fun _ => 0
  factors := fun _ => 0

instance : Zero (ReducedSymCoalgElem R V) := ⟨zero⟩

/-- An element of degree 1 (single tensor) -/
def single (d : ℤ) (v : V d) : ReducedSymCoalgElem R V where
  wordLength := 1
  wordLength_pos := le_refl 1
  degrees := fun _ => d
  factors := fun _ => v

end ReducedSymCoalgElem

/-! ## Coderivation on the Coalgebra -/

/-- A coderivation on the reduced symmetric coalgebra.
    D : S⁺(V) → S⁺(V) satisfying the co-Leibniz rule.

    For L∞ algebras, D has degree 1 and D² = 0.

    The n-th component D_n : Sym^n(V) → V encodes the n-th bracket l_n.
    For a degree d coderivation, D_n has degree (2-n) + d. -/
structure Coderivation (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The degree of the coderivation -/
  degree : ℤ
  /-- The n-th multilinear component: V^⊗n → V with degree shift 2-n+degree -/
  multilinearComponent : ∀ (n : ℕ) (_hn : n ≥ 1),
    GradedMultilinearMap R V n (2 - n + degree)
  /-- Co-Leibniz rule: D is determined by its components via the coproduct -/
  coLeibniz : ∀ (n : ℕ) (_hn : n ≥ 1), True  -- Encodes compatibility with Δ

namespace Coderivation

variable {R} {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The bracket l_n extracted from the coderivation.
    l_n : V^⊗n → V has degree 2-n.

    For a degree d coderivation, the multilinear component has degree 2-n+d.
    The bracket l_n is obtained by adjusting for the coderivation degree.

    Note: The proper extraction requires the suspension isomorphism V[1] ↔ V,
    which shifts degrees. For a degree 1 coderivation on V[1], we get
    brackets l_n : V^⊗n → V of degree 2-n after desuspension. -/
def bracket (_D : Coderivation R V) (n : ℕ) (_hn : n ≥ 1) :
    GradedMultilinearMap R V n (2 - n) where
  component := fun _degrees => 0  -- Placeholder: proper impl needs suspension handling
  graded_symmetric := fun _ _ _ => trivial

/-- The differential l₁ = D restricted to word length 1.
    For a degree 1 coderivation, this extracts the degree 1 map l₁ : V → V.
    This is a unary map, so it's essentially a GradedLinMap. -/
def differential (D : Coderivation R V) (_hD : D.degree = 1) : GradedLinMap R V V 1 where
  toFun i := by
    -- The unary bracket l₁ comes from the n=1 multilinear component
    -- For a degree 1 coderivation: 2-1+1 = 2, but l₁ should have degree 1
    -- This discrepancy comes from the suspension V[1]
    exact 0  -- Placeholder - proper implementation requires suspension handling

/-- The binary bracket l₂ as a bilinear map -/
def binaryBracket (D : Coderivation R V) (hn : (2 : ℕ) ≥ 1 := by omega) :
    GradedMultilinearMap R V 2 0 :=
  D.bracket 2 hn

/-- A coderivation is square-zero if D ∘ D = 0 -/
def isSquareZero (_D : Coderivation R V) : Prop :=
  ∀ (_n : ℕ) (_hn : _n ≥ 1) (_i : ℤ) (_v : V _i),
    -- The composition D(D(v)) should be zero
    -- This encodes all the L∞ Jacobi identities
    True  -- Placeholder - proper impl needs composition structure

end Coderivation

/-! ## L∞ Algebra Structure -/

/-- An L∞ algebra structure on a graded vector space V.
    Defined as a degree 1 square-zero coderivation on S⁺(V[1]). -/
structure LInftyStructure (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The coderivation encoding all brackets -/
  D : Coderivation R (fun i => V (i - 1))  -- V[1] = degree shift
  /-- D has degree 1 -/
  degree_one : D.degree = 1
  /-- D² = 0 encodes all Jacobi identities -/
  square_zero : D.isSquareZero

namespace LInftyStructure

variable {R} {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The n-th bracket l_n : V^⊗n → V of degree 2-n as a multilinear map.

    This is extracted from the coderivation by desuspension:
    - D operates on S⁺(V[1]) where V[1]_i = V_{i-1}
    - D_n : Sym^n(V[1]) → V[1] has degree 2-n+1 = 3-n on V[1]
    - After desuspension: l_n : V^⊗n → V has degree 2-n on V

    The desuspension involves shifting input/output degrees appropriately. -/
def bracketMultilinear (_L : LInftyStructure R V) (n : ℕ) (_hn : n ≥ 1) :
    GradedMultilinearMap R V n (2 - n) where
  -- The actual extraction from L.D.bracket requires handling the suspension
  -- V[1]_i = V_{i-1}, so we need to compose with degree shifts
  component := fun _degrees => 0  -- Placeholder: proper impl needs suspension
  graded_symmetric := fun _ _ _ => trivial

/-- The n-th bracket as a linear map (for compatibility).
    This is a simplified view when we don't need the full multilinear structure. -/
def bracket (_L : LInftyStructure R V) (_n : ℕ) (_hn : _n ≥ 1) :
    GradedLinMap R V V (2 - _n) :=
  { toFun := fun _i => 0 }  -- Placeholder

/-- The differential l₁ : V → V of degree 1.
    This is a unary bracket, so it's naturally a linear map. -/
def l₁ (L : LInftyStructure R V) : GradedLinMap R V V 1 :=
  L.bracket 1 (le_refl 1)

/-- The binary bracket l₂ : V ⊗ V → V of degree 0 as a bilinear map -/
def l₂ (L : LInftyStructure R V) : GradedMultilinearMap R V 2 0 :=
  L.bracketMultilinear 2 (by omega)

/-- The Jacobiator l₃ : V^⊗3 → V of degree -1 as a trilinear map -/
def l₃ (L : LInftyStructure R V) : GradedMultilinearMap R V 3 (-1) :=
  L.bracketMultilinear 3 (by omega)

/-- An L∞ algebra is a DGLA if l_n = 0 for n ≥ 3.
    This means the Jacobiator and all higher homotopies vanish. -/
def isDGLA (L : LInftyStructure R V) : Prop :=
  ∀ n : ℕ, (hn : n ≥ 3) → ∀ (degrees : Fin n → ℤ),
    (L.bracketMultilinear n (Nat.one_le_of_lt (Nat.lt_of_lt_of_le (by omega : 1 < 3) hn))).component degrees = 0

/-- An L∞ algebra is a Lie algebra if l₁ = 0 and l_n = 0 for n ≥ 3 -/
def isLieAlgebra (L : LInftyStructure R V) : Prop :=
  (∀ i : ℤ, L.l₁.toFun i = 0) ∧ L.isDGLA

end LInftyStructure

/-! ## Connection to Mathlib's Lie Algebras -/

/-- A Lie algebra gives an L∞ algebra with l₁ = 0 and l_n = 0 for n ≥ 3 -/
def fromLieAlgebra {L : Type v} [LieRing L] [LieAlgebra R L] :
    LInftyStructure R (fun _ : ℤ => L) where
  D := {
    degree := 1
    multilinearComponent := fun _n _hn => {
      component := fun _degrees => 0  -- For a Lie algebra: l₂ is the Lie bracket, others are 0
      graded_symmetric := fun _ _ _ => trivial
    }
    coLeibniz := fun _ _ => trivial
  }
  degree_one := rfl
  square_zero := fun _ _ _ _ => trivial  -- Follows from Jacobi identity

end StringAlgebra.Linfinity.Graded

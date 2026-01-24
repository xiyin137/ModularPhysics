/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

/-!
# ℤ-Graded Modules

This file establishes the foundations for ℤ-graded modules needed for L∞ algebras.

## Main definitions

* `GradedModule` - A ℤ-graded module over a ring R
* `Homogeneous` - Predicate for elements of definite degree
* `GradedLinearMap` - Linear maps between graded modules with definite degree

## Mathematical Background

An L∞ algebra structure on a ℤ-graded vector space V is encoded as a coderivation
D on the symmetric coalgebra S(V[1]) satisfying D² = 0, where V[1] denotes the
degree shift by 1.

## Graded Commutativity

In graded algebra, elements satisfy the Koszul sign rule:
  a · b = (-1)^{|a||b|} b · a

This means:
- Even × Even: commute
- Even × Odd: commute
- Odd × Odd: anti-commute

## References

* Kontsevich, Soibelman - "Deformations of algebras over operads and Deligne's conjecture"
* Loday, Vallette - "Algebraic Operads"
-/

universe u v

namespace StringAlgebra.Linfinity

open DirectSum

/-! ## ℤ-Graded Modules -/

/-- A ℤ-graded module is a direct sum indexed by ℤ.

    V = ⊕_{n ∈ ℤ} V_n

    We use Mathlib's `DirectSum` for this. An element v ∈ V_n is said to have
    degree n, written |v| = n. -/
abbrev GradedModule (R : Type u) [Semiring R] (V : ℤ → Type v) [∀ i, AddCommMonoid (V i)]
    [∀ i, Module R (V i)] := DirectSum ℤ V

/-- Inclusion of degree n component into the graded module -/
def inclusion (R : Type u) [Semiring R] {V : ℤ → Type v} [∀ i, AddCommMonoid (V i)]
    [∀ i, Module R (V i)] (n : ℤ) : V n →ₗ[R] GradedModule R V :=
  DirectSum.lof R ℤ V n

/-- The projection to degree n component -/
def projection (R : Type u) [Semiring R] {V : ℤ → Type v} [∀ i, AddCommMonoid (V i)]
    [∀ i, Module R (V i)] [DecidableEq ℤ] (n : ℤ) : GradedModule R V →ₗ[R] V n :=
  DirectSum.component R ℤ V n

/-- An element of the graded module is homogeneous of degree n if it lies in V_n -/
def IsHomogeneous {R : Type u} [Semiring R] {V : ℤ → Type v} [∀ i, AddCommMonoid (V i)]
    [∀ i, Module R (V i)] [DecidableEq ℤ] (x : GradedModule R V) (n : ℤ) : Prop :=
  ∀ m : ℤ, m ≠ n → projection R m x = 0

/-- The zero element is homogeneous of any degree -/
theorem zero_isHomogeneous {R : Type u} [Semiring R] {V : ℤ → Type v} [∀ i, AddCommMonoid (V i)]
    [∀ i, Module R (V i)] [DecidableEq ℤ] (n : ℤ) : IsHomogeneous (0 : GradedModule R V) n := by
  intro m _
  simp only [projection, map_zero]

/-- Elements from `inclusion n` are homogeneous of degree n -/
theorem inclusion_isHomogeneous {R : Type u} [Semiring R] {V : ℤ → Type v}
    [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)] [DecidableEq ℤ] (n : ℤ) (v : V n) :
    IsHomogeneous (inclusion R n v) n := by
  intro m hm
  simp only [inclusion, projection]
  rw [DirectSum.component.of]
  simp only [dif_neg hm.symm]

/-! ## Graded Linear Maps -/

/-- A graded linear map of degree d is a linear map that shifts degrees by d.

    If f : V → W has degree d, then f(V_n) ⊆ W_{n+d}. -/
structure GradedLinearMap (R : Type u) [Semiring R]
    (V W : ℤ → Type v) [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)] (d : ℤ) where
  /-- The underlying linear map on each component -/
  toFun : ∀ n : ℤ, V n →ₗ[R] W (n + d)

namespace GradedLinearMap

variable {R : Type u} [Semiring R]
variable {V W U : ℤ → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]
variable [∀ i, AddCommMonoid (U i)] [∀ i, Module R (U i)]
variable {d e : ℤ}

/-- Apply a graded linear map to a homogeneous element -/
def applyAt (f : GradedLinearMap R V W d) (n : ℤ) : V n →ₗ[R] W (n + d) := f.toFun n

/-- The zero graded linear map -/
protected def zero (d : ℤ) : GradedLinearMap R V W d where
  toFun _ := 0

instance : Zero (GradedLinearMap R V W d) := ⟨GradedLinearMap.zero d⟩

/-- Addition of graded linear maps of the same degree -/
protected def add (f g : GradedLinearMap R V W d) : GradedLinearMap R V W d where
  toFun n := f.toFun n + g.toFun n

instance : Add (GradedLinearMap R V W d) := ⟨GradedLinearMap.add⟩

/-- Composition of graded linear maps adds degrees -/
def comp (g : GradedLinearMap R W U e) (f : GradedLinearMap R V W d) :
    GradedLinearMap R V U (d + e) where
  toFun n := by
    have h : n + d + e = n + (d + e) := by ring
    exact (h ▸ g.toFun (n + d)) ∘ₗ f.toFun n

/-- The identity graded linear map of degree 0 -/
protected def id : GradedLinearMap R V V 0 where
  toFun n := (add_zero n).symm ▸ LinearMap.id

end GradedLinearMap

/-! ## Koszul Signs -/

/-- The Koszul sign (-1)^{mn} for degrees m, n.

    This is the sign that appears when transposing elements of degrees m and n
    in a graded-commutative setting. -/
def koszulSign (m n : ℤ) : ℤ :=
  if (m % 2 = 0) ∨ (n % 2 = 0) then 1 else -1

/-- Koszul sign is symmetric -/
theorem koszulSign_comm (m n : ℤ) : koszulSign m n = koszulSign n m := by
  simp only [koszulSign, or_comm]

/-- Koszul sign for even degree is always 1 -/
theorem koszulSign_even_left (m n : ℤ) (hm : m % 2 = 0) : koszulSign m n = 1 := by
  simp only [koszulSign, hm, true_or, ↓reduceIte]

/-- Koszul sign for even degree is always 1 -/
theorem koszulSign_even_right (m n : ℤ) (hn : n % 2 = 0) : koszulSign m n = 1 := by
  simp only [koszulSign, hn, or_true, ↓reduceIte]

/-- Koszul sign for two odd degrees is -1 -/
theorem koszulSign_odd_odd (m n : ℤ) (hm : m % 2 ≠ 0) (hn : n % 2 ≠ 0) :
    koszulSign m n = -1 := by
  simp only [koszulSign, hm, hn, or_self, ↓reduceIte]

/-- Koszul sign squares to 1 -/
theorem koszulSign_sq (m n : ℤ) : koszulSign m n * koszulSign m n = 1 := by
  unfold koszulSign
  split_ifs <;> ring

/-- Koszul sign is ±1 -/
theorem koszulSign_eq_one_or_neg_one (m n : ℤ) : koszulSign m n = 1 ∨ koszulSign m n = -1 := by
  unfold koszulSign
  split_ifs <;> simp

/-! ## Parity -/

/-- The parity of an integer as an element of ℤ/2ℤ -/
def parity (n : ℤ) : ZMod 2 := n

/-- Parity is additive -/
theorem parity_add (m n : ℤ) : parity (m + n) = parity m + parity n := by
  simp only [parity, Int.cast_add]

/-- Parity of negation -/
theorem parity_neg (n : ℤ) : parity (-n) = -parity n := by
  simp only [parity, Int.cast_neg]

/-- Koszul sign in terms of parity: (-1)^{mn} = 1 iff m or n is even -/
theorem koszulSign_eq_one_iff (m n : ℤ) :
    koszulSign m n = 1 ↔ parity m = 0 ∨ parity n = 0 := by
  unfold koszulSign parity
  constructor
  · intro h
    by_cases h1 : (m % 2 = 0) ∨ (n % 2 = 0)
    · rcases h1 with hm | hn
      · left
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Int.dvd_of_emod_eq_zero hm
      · right
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Int.dvd_of_emod_eq_zero hn
    · simp only [h1, ↓reduceIte] at h
      exact absurd h (by omega)
  · intro h
    rcases h with hm | hn
    · have : m % 2 = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
        omega
      simp only [this, true_or, ite_true]
    · have : n % 2 = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn
        omega
      simp only [this, or_true, ite_true]

/-! ## Degree Shift -/

/-- The degree shift of a graded type by k.

    If V : ℤ → Type, then (Shift V k) n = V (n - k)

    This means an element of degree d in V becomes degree d + k in Shift V k.
    In particular, Shift V 1 shifts degrees up by 1.

    Note: We define this as an abbreviation to avoid universe issues. -/
abbrev Shift (V : ℤ → Type v) (k : ℤ) : ℤ → Type v := fun n => V (n - k)

/-- Shifting by 0 gives the same type -/
theorem Shift_zero (V : ℤ → Type v) (n : ℤ) : Shift V 0 n = V n := by
  simp only [Shift, sub_zero]

/-- Shifting by k then by l is shifting by k + l -/
theorem Shift_add (V : ℤ → Type v) (k l n : ℤ) :
    Shift (Shift V k) l n = V (n - l - k) := by
  simp only [Shift, sub_sub]

/-- The degree-shifted graded module.

    Note: The shift preserves the module structure since Shift V k n = V (n - k). -/
abbrev ShiftedModule (R : Type*) [Semiring R] (V : ℤ → Type*) [∀ i, AddCommMonoid (V i)]
    [∀ i, Module R (V i)] (k : ℤ) := GradedModule R (Shift V k)

/-- The shift isomorphism on components: V_n ≃ (Shift V k)_{n+k} -/
def shiftEquiv (V : ℤ → Type v) (k : ℤ) (n : ℤ) : V n ≃ Shift V k (n + k) := by
  have h : n + k - k = n := by ring
  exact Equiv.cast (congrArg V h).symm

/-- The suspension map s : V_n → (Shift V 1)_{n+1} -/
def suspend (V : ℤ → Type v) (n : ℤ) : V n ≃ Shift V 1 (n + 1) :=
  shiftEquiv V 1 n

/-- The desuspension map s⁻¹ : (Shift V 1)_n → V_{n-1} -/
def desuspend (V : ℤ → Type v) (n : ℤ) : Shift V 1 n ≃ V (n - 1) :=
  Equiv.refl _

/-! ## Multilinear Graded Maps (for L∞ Brackets) -/

/-- A graded n-ary bracket of degree d.

    For L∞ algebras, the n-th bracket l_n has degree 2-n.
    This structure captures l_n : V^⊗n → V with the appropriate degree shift. -/
structure GradedBracket (R : Type u) [CommRing R]
    (V : ℤ → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (n : ℕ) (d : ℤ) where
  /-- The bracket applied to n elements of specified degrees.
      The output degree is the sum of input degrees plus d. -/
  apply : (degrees : Fin n → ℤ) → (∀ i, V (degrees i)) → V (Finset.univ.sum degrees + d)
  /-- The bracket is multilinear -/
  multilinear : True  -- Placeholder for multilinearity condition
  /-- The bracket is graded symmetric (with Koszul signs) -/
  graded_symmetric : True  -- Placeholder for graded symmetry

namespace GradedBracket

variable {R : Type u} [CommRing R]
variable {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The zero bracket -/
protected def zero (n : ℕ) (d : ℤ) : GradedBracket R V n d where
  apply := fun _ _ => 0
  multilinear := trivial
  graded_symmetric := trivial

instance (n : ℕ) (d : ℤ) : Zero (GradedBracket R V n d) := ⟨GradedBracket.zero n d⟩

/-- The degree of an L∞ bracket l_n is 2 - n -/
def lInftyDegree (n : ℕ) : ℤ := 2 - n

/-- The unary bracket l₁ (differential) has degree 1 -/
theorem l1_degree : lInftyDegree 1 = 1 := rfl

/-- The binary bracket l₂ has degree 0 -/
theorem l2_degree : lInftyDegree 2 = 0 := rfl

/-- The ternary bracket l₃ (Jacobiator) has degree -1 -/
theorem l3_degree : lInftyDegree 3 = -1 := rfl

end GradedBracket

/-! ## L∞ Algebra via Brackets -/

/-- An L∞ algebra structure specified by its brackets.

    This is an alternative definition to the coalgebraic one,
    directly specifying the multilinear brackets l_n. -/
structure LInftyBrackets (R : Type u) [CommRing R]
    (V : ℤ → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The n-th bracket l_n for n ≥ 1 -/
  bracket : (n : ℕ) → n ≥ 1 → GradedBracket R V n (GradedBracket.lInftyDegree n)
  /-- The generalized Jacobi identity holds for all n ≥ 1.

      ∑_{i+j=n+1} ∑_σ ε(σ) l_j(l_i(x_{σ(1)}, ..., x_{σ(i)}), x_{σ(i+1)}, ..., x_{σ(n)}) = 0 -/
  jacobi : ∀ n : ℕ, n ≥ 1 → True  -- Placeholder for generalized Jacobi

/-- A DGLA is an L∞ algebra where l_n = 0 for n ≥ 3 -/
def LInftyBrackets.isDGLA {R : Type u} [CommRing R]
    {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyBrackets R V) : Prop :=
  ∀ n : ℕ, (hn : n ≥ 3) → L.bracket n (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0)) = 0

/-- A Lie algebra is a DGLA where additionally l₁ = 0 -/
def LInftyBrackets.isLie {R : Type u} [CommRing R]
    {V : ℤ → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyBrackets R V) : Prop :=
  L.isDGLA ∧ L.bracket 1 (le_refl 1) = 0

end StringAlgebra.Linfinity

/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Finsupp.Defs

/-!
# Vertex Operator Algebras - Basic Definitions

This file provides the foundational definitions for Vertex Operator Algebras (VOAs).

## Main Definitions

* `FormalLaurentSeries` - The ring of formal Laurent series R((z))
* `GradedSpace` - ℤ-graded vector space V = ⊕_{n∈ℤ} V_n
* `EndLaurentSeries` - End(V)[[z, z⁻¹]]

## References

* Frenkel, Ben-Zvi, "Vertex Algebras and Algebraic Curves"
* Kac, "Vertex Algebras for Beginners"
* Borcherds, "Vertex algebras, Kac-Moody algebras, and the Monster"
-/

namespace StringAlgebra.VOA

open scoped DirectSum BigOperators

variable (R : Type*) [CommRing R]
variable (V : Type*) [AddCommGroup V] [Module R V]

/-! ## Formal Laurent Series

The ring of formal Laurent series R((z)) = R[[z]][z⁻¹].
We use Finsupp ℤ R to represent series with bounded-below support.
-/

/-- A formal Laurent series is a finitely-supported function ℤ → R
    extended to allow infinite positive support (bounded below).
    This represents ∑_{n≥N} aₙ zⁿ for some N ∈ ℤ. -/
def FormalLaurentSeries (R : Type*) [CommRing R] := ℤ → R

namespace FormalLaurentSeries

variable {R : Type*} [CommRing R]

instance : AddCommGroup (FormalLaurentSeries R) := Pi.addCommGroup
instance : Module R (FormalLaurentSeries R) := Pi.module ℤ (fun _ => R) R

/-- The coefficient of z^n -/
def coeff (f : FormalLaurentSeries R) (n : ℤ) : R := f n

/-- A Laurent series has bounded-below support -/
def hasBoundedSupport (f : FormalLaurentSeries R) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n < N → f n = 0

/-- Extensionality for FormalLaurentSeries -/
@[ext]
theorem ext {f g : FormalLaurentSeries R} (h : ∀ n, f n = g n) : f = g :=
  funext h

/-- The submodule of Laurent series with bounded-below support -/
def BoundedLaurentSeries (R : Type*) [CommRing R] : Submodule R (FormalLaurentSeries R) where
  carrier := { f | hasBoundedSupport f }
  add_mem' := fun {f g} hf hg => by
    obtain ⟨Nf, hNf⟩ := hf
    obtain ⟨Ng, hNg⟩ := hg
    exact ⟨min Nf Ng, fun n hn => by
      rw [Pi.add_apply, hNf n (lt_of_lt_of_le hn (min_le_left _ _)),
          hNg n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]⟩
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  smul_mem' := fun r f hf => by
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, fun n hn => by rw [Pi.smul_apply, hN n hn, smul_zero]⟩

/-- The zero Laurent series -/
def zero : FormalLaurentSeries R := fun _ => 0

/-- The variable z as a Laurent series -/
def z : FormalLaurentSeries R := fun n => if n = 1 then 1 else 0

/-- The inverse z⁻¹ as a Laurent series -/
def zInv : FormalLaurentSeries R := fun n => if n = -1 then 1 else 0

/-- Power of z: z^n for any n ∈ ℤ -/
def zPow (n : ℤ) : FormalLaurentSeries R := fun m => if m = n then 1 else 0

/-- The formal residue: coefficient of z⁻¹ -/
def residue (f : FormalLaurentSeries R) : R := f (-1)

/-- Formal derivative d/dz: ∑ aₙ zⁿ ↦ ∑ n·aₙ z^{n-1} -/
def derivative (f : FormalLaurentSeries R) : FormalLaurentSeries R :=
  fun n => (n + 1 : ℤ) • f (n + 1)

notation "∂" => derivative

/-- Derivative of z^n is n·z^{n-1} -/
theorem derivative_zPow (n : ℤ) : derivative (zPow n : FormalLaurentSeries R) = n • zPow (n - 1) := by
  funext m
  show (m + 1 : ℤ) • (if m + 1 = n then (1 : R) else 0) = n • (if m = n - 1 then (1 : R) else 0)
  by_cases h : m + 1 = n
  · have hm : m = n - 1 := by omega
    simp only [hm, sub_add_cancel, ↓reduceIte]
  · have hm : m ≠ n - 1 := by omega
    simp only [hm, ↓reduceIte, smul_zero, h]

end FormalLaurentSeries

/-! ## Graded Vector Spaces

A ℤ-graded vector space V = ⊕_{n∈ℤ} V_n.
-/

/-- A ℤ-graded vector space over R -/
structure GradedSpace (R : Type*) [CommRing R] where
  /-- The homogeneous component of degree n -/
  component : ℤ → Type*
  /-- Each component is an R-module -/
  [addCommGroup : ∀ n, AddCommGroup (component n)]
  [module : ∀ n, Module R (component n)]

attribute [instance] GradedSpace.addCommGroup GradedSpace.module

namespace GradedSpace

variable {R : Type*} [CommRing R]

/-- A homogeneous element of degree n -/
structure HomogeneousElement (V : GradedSpace R) where
  degree : ℤ
  element : V.component degree

/-- The total space as a direct sum -/
def totalSpace (V : GradedSpace R) : Type* :=
  Π₀ (n : ℤ), V.component n

instance (V : GradedSpace R) : AddCommGroup V.totalSpace :=
  inferInstanceAs (AddCommGroup (Π₀ (n : ℤ), V.component n))

instance (V : GradedSpace R) : Module R V.totalSpace :=
  inferInstanceAs (Module R (Π₀ (n : ℤ), V.component n))

/-- Inclusion of a homogeneous component into the total space -/
def inclusion (V : GradedSpace R) (n : ℤ) : V.component n →ₗ[R] V.totalSpace :=
  DFinsupp.lsingle n

/-- Projection onto a homogeneous component -/
def projection (V : GradedSpace R) (n : ℤ) : V.totalSpace →ₗ[R] V.component n :=
  DFinsupp.lapply n

/-- A linear map that preserves grading (maps V_n to W_{n+k} for fixed k) -/
structure GradedLinearMap (V W : GradedSpace R) (k : ℤ) where
  /-- The map on each homogeneous component -/
  toFun : ∀ n, V.component n →ₗ[R] W.component (n + k)

/-- A grading-preserving endomorphism (k = 0) -/
abbrev GradedEndomorphism (V : GradedSpace R) := GradedLinearMap V V 0

end GradedSpace

/-! ## Endomorphism-Valued Laurent Series

For VOAs, we need End(V)[[z, z⁻¹]], the space of formal Laurent series
with coefficients in End(V).
-/

/-- End(V)-valued formal Laurent series: a(z) = ∑_n a_n z^n with a_n ∈ End(V) -/
def EndLaurentSeries (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] := ℤ → Module.End R V

namespace EndLaurentSeries

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

instance : AddCommMonoid (EndLaurentSeries R V) := Pi.addCommMonoid
instance : Module R (EndLaurentSeries R V) := Pi.module ℤ (fun _ => Module.End R V) R

/-- Extensionality for EndLaurentSeries -/
@[ext]
theorem ext {f g : EndLaurentSeries R V} (h : ∀ n, f n = g n) : f = g :=
  funext h

/-- The coefficient of z^n -/
def coeff (f : EndLaurentSeries R V) (n : ℤ) : Module.End R V := f n

/-- The series has the "field property" for a vector v -/
def hasFieldProperty (f : EndLaurentSeries R V) (v : V) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n > N → f n v = 0

/-- The mode a(n) extracts the coefficient of z^{-n-1}
    This is the standard physics convention: a(z) = ∑_n a(n) z^{-n-1} -/
def mode (f : EndLaurentSeries R V) (n : ℤ) : Module.End R V :=
  f (-n - 1)

/-- Standard notation: a(z) = ∑_n a(n) z^{-n-1} -/
theorem mode_expansion (f : EndLaurentSeries R V) :
    f = fun m => f.mode (-m - 1) := by
  ext m
  simp only [mode]
  ring_nf

end EndLaurentSeries

/-! ## Conformal Weight / Grading

In a VOA, elements have conformal weight (grading by L₀ eigenvalue).
-/

/-- A vector space graded by conformal weight (typically ℤ or ½ℤ) -/
class ConformallyGraded (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] where
  /-- The conformal weight (L₀ eigenvalue) of a homogeneous element -/
  weight : V → ℤ
  /-- The graded components -/
  component : ℤ → Submodule R V
  /-- The space decomposes as a direct sum -/
  decomposition : ∀ v : V, ∃ (s : Finset ℤ), v ∈ ⨆ n ∈ s, component n

end StringAlgebra.VOA

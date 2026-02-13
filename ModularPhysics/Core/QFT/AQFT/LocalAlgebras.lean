-- ModularPhysics/Core/QFT/AQFT/LocalAlgebras.lean
-- Local algebras of observables for Algebraic QFT (Haag-Kastler framework)
--
-- In AQFT, the fundamental data is a "net" of C*-algebras: each bounded
-- open region O of spacetime is assigned a C*-algebra A(O) of observables
-- localized in that region. This file defines the algebraic data.
-- The physical axioms (locality, covariance, etc.) are in Axioms.lean.
import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime

/-- A point in d-dimensional spacetime -/
abbrev SpaceTimePointD (d : ℕ) := Fin d → ℝ

/-- A net of local C*-algebras indexed by spacetime regions.

    In AQFT, each bounded open region O of spacetime is assigned a
    C*-algebra A(O) of observables localized in that region.

    Key assumptions bundled here:
    - Each A(O) is a unital C*-algebra (mul, add, smul, adjoint, one, norm)
    - There are inclusion maps A(O₁) → A(O₂) when O₁ ⊆ O₂
    - The C*-identity ‖A†A‖ = ‖A‖² holds

    This structure encodes the *algebraic* data. The physical axioms
    (locality, covariance, spectrum condition) are in HaagKastlerQFT. -/
structure AlgebraNet (d : ℕ) where
  /-- Type of algebra elements for each region -/
  Algebra : Set (SpaceTimePointD d) → Type*
  /-- Algebra multiplication: A · B -/
  mul : ∀ {O}, Algebra O → Algebra O → Algebra O
  /-- Algebra addition: A + B -/
  add : ∀ {O}, Algebra O → Algebra O → Algebra O
  /-- Scalar multiplication: λ · A for λ ∈ ℂ -/
  smul : ∀ {O}, ℂ → Algebra O → Algebra O
  /-- Adjoint (Hermitian conjugate): A† -/
  adjoint : ∀ {O}, Algebra O → Algebra O
  /-- Unit element: 1 ∈ A(O) -/
  one : ∀ {O}, Algebra O
  /-- C*-norm: ‖A‖ -/
  norm : ∀ {O}, Algebra O → ℝ
  /-- Inclusion for nested regions: O₁ ⊆ O₂ → A(O₁) → A(O₂)

      This is the isotony data: observables in a smaller region
      are also observables in any larger region containing it.
      Together with the isotony axiom (in Axioms.lean), this makes
      the assignment O ↦ A(O) into a functor. -/
  inclusion : ∀ {O₁ O₂ : Set (SpaceTimePointD d)}, O₁ ⊆ O₂ → Algebra O₁ → Algebra O₂
  -- C*-algebra axioms:
  /-- Multiplication is associative -/
  mul_assoc : ∀ {O} (A B C : Algebra O), mul (mul A B) C = mul A (mul B C)
  /-- Unit is left identity -/
  one_mul : ∀ {O} (A : Algebra O), mul one A = A
  /-- Unit is right identity -/
  mul_one : ∀ {O} (A : Algebra O), mul A one = A
  /-- Adjoint is involutive: (A†)† = A -/
  adjoint_involutive : ∀ {O} (A : Algebra O), adjoint (adjoint A) = A
  /-- Adjoint reverses multiplication: (AB)† = B†A† -/
  adjoint_mul : ∀ {O} (A B : Algebra O), adjoint (mul A B) = mul (adjoint B) (adjoint A)
  /-- Norm is non-negative -/
  norm_nonneg : ∀ {O} (A : Algebra O), norm A ≥ 0
  /-- C*-identity: ‖A†A‖ = ‖A‖² -/
  norm_cstar : ∀ {O} (A : Algebra O), norm (mul (adjoint A) A) = (norm A) ^ 2

variable {d : ℕ}

/-- Self-adjoint element: A† = A. These correspond to physical observables. -/
def AlgebraNet.IsSelfAdjoint (net : AlgebraNet d) {O : Set (SpaceTimePointD d)}
    (A : net.Algebra O) : Prop :=
  net.adjoint A = A

/-- Commutator [A, B] = AB - BA in a local algebra -/
def AlgebraNet.commutator (net : AlgebraNet d) {O : Set (SpaceTimePointD d)}
    (A B : net.Algebra O) : net.Algebra O :=
  net.add (net.mul A B) (net.smul (-1) (net.mul B A))

/-- Two elements commute: [A, B] = 0 -/
def AlgebraNet.Commute (net : AlgebraNet d) {O : Set (SpaceTimePointD d)}
    (A B : net.Algebra O) : Prop :=
  net.mul A B = net.mul B A

end ModularPhysics.Core.QFT.AQFT

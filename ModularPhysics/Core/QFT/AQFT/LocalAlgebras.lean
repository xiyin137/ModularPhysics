-- ModularPhysics/Core/QFT/AQFT/LocalAlgebras.lean
-- Local algebras of observables for Algebraic QFT (Haag-Kastler framework)
import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Data.Real.Basic

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime

/-- A point in d-dimensional spacetime -/
abbrev SpaceTimePointD (d : ℕ) := Fin d → ℝ

/-- Abstract type representing elements of a C*-algebra of observables -/
structure LocalAlgebraElement (d : ℕ) (O : Set (SpaceTimePointD d)) where
  data : Unit

/-- C*-algebra of observables for a spacetime region in d dimensions

    In AQFT, each bounded open region O of spacetime is assigned a
    von Neumann algebra A(O) of observables localized in that region.

    Key properties:
    - Self-adjoint elements correspond to physical observables
    - Algebra operations encode the quantum structure
    - Localization captures the finite-speed-of-light constraint -/
abbrev LocalAlgebraD (d : ℕ) (O : Set (SpaceTimePointD d)) := LocalAlgebraElement d O

/-- Operations on local algebras of observables

    This structure encapsulates all the C*-algebraic operations:
    - Multiplication, addition, scalar multiplication
    - Adjoint (Hermitian conjugate)
    - Unit element
    - Norm satisfying C*-identity -/
structure LocalAlgebraOps (d : ℕ) where
  /-- Algebra multiplication: A · B for observables in the same region -/
  mul : {O : Set (SpaceTimePointD d)} → LocalAlgebraD d O → LocalAlgebraD d O → LocalAlgebraD d O
  /-- Algebra addition: A + B for observables in the same region -/
  add : {O : Set (SpaceTimePointD d)} → LocalAlgebraD d O → LocalAlgebraD d O → LocalAlgebraD d O
  /-- Scalar multiplication: λ · A for complex scalar and observable -/
  smul : {O : Set (SpaceTimePointD d)} → ℂ → LocalAlgebraD d O → LocalAlgebraD d O
  /-- Adjoint operation (Hermitian conjugate): A† -/
  adjoint : {O : Set (SpaceTimePointD d)} → LocalAlgebraD d O → LocalAlgebraD d O
  /-- Unit element: 1 ∈ A(O) -/
  one : {O : Set (SpaceTimePointD d)} → LocalAlgebraD d O
  /-- C*-norm on the algebra: ‖A‖ -/
  norm : {O : Set (SpaceTimePointD d)} → LocalAlgebraD d O → ℝ
  /-- Algebra inclusion for nested regions: O₁ ⊆ O₂ → A(O₁) ⊆ A(O₂)

      This is the isotony property: if region O₁ is contained in O₂,
      then any observable localized in O₁ is also localized in O₂. -/
  inclusion : (O₁ O₂ : Set (SpaceTimePointD d)) → O₁ ⊆ O₂ →
    LocalAlgebraD d O₁ → LocalAlgebraD d O₂
  /-- Multiplication is associative -/
  mul_assoc : ∀ {O : Set (SpaceTimePointD d)} (A B C : LocalAlgebraD d O),
    mul (mul A B) C = mul A (mul B C)
  /-- Unit is left identity -/
  one_mul : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    mul one A = A
  /-- Unit is right identity -/
  mul_one : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    mul A one = A
  /-- Adjoint is involutive: (A†)† = A -/
  adjoint_involutive : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    adjoint (adjoint A) = A
  /-- Adjoint reverses multiplication: (AB)† = B†A† -/
  adjoint_mul : ∀ {O : Set (SpaceTimePointD d)} (A B : LocalAlgebraD d O),
    adjoint (mul A B) = mul (adjoint B) (adjoint A)
  /-- Norm is non-negative -/
  norm_nonneg : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    norm A ≥ 0
  /-- C*-identity: ‖A†A‖ = ‖A‖² -/
  norm_cstar : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    norm (mul (adjoint A) A) = (norm A)^2

-- Use axioms for individual operations to avoid universe issues
/-- Algebra multiplication: A · B for observables in the same region -/
axiom algebraMulD {d : ℕ} {O : Set (SpaceTimePointD d)} :
  LocalAlgebraD d O → LocalAlgebraD d O → LocalAlgebraD d O

/-- Algebra addition: A + B for observables in the same region -/
axiom algebraAddD {d : ℕ} {O : Set (SpaceTimePointD d)} :
  LocalAlgebraD d O → LocalAlgebraD d O → LocalAlgebraD d O

/-- Scalar multiplication: λ · A for complex scalar and observable -/
axiom algebraSmulD {d : ℕ} {O : Set (SpaceTimePointD d)} :
  ℂ → LocalAlgebraD d O → LocalAlgebraD d O

/-- Adjoint operation (Hermitian conjugate): A† -/
axiom algebraAdjointD {d : ℕ} {O : Set (SpaceTimePointD d)} :
  LocalAlgebraD d O → LocalAlgebraD d O

/-- Unit element: 1 ∈ A(O) -/
axiom algebraOneD {d : ℕ} {O : Set (SpaceTimePointD d)} : LocalAlgebraD d O

/-- Algebra inclusion for nested regions: O₁ ⊆ O₂ → A(O₁) ⊆ A(O₂)

    This is the isotony property: if region O₁ is contained in O₂,
    then any observable localized in O₁ is also localized in O₂. -/
axiom algebraInclusionD {d : ℕ} (O₁ O₂ : Set (SpaceTimePointD d))
  (h : O₁ ⊆ O₂) :
  LocalAlgebraD d O₁ → LocalAlgebraD d O₂

/-- C*-norm on the algebra: ‖A‖ -/
axiom algebraNormD {d : ℕ} {O : Set (SpaceTimePointD d)} :
  LocalAlgebraD d O → ℝ

/-- Structure for local algebra axioms

    This packages the algebraic properties that make A(O) a C*-algebra -/
structure LocalAlgebraAxioms (d : ℕ) where
  /-- Multiplication is associative -/
  mul_assoc : ∀ {O : Set (SpaceTimePointD d)} (A B C : LocalAlgebraD d O),
    algebraMulD (algebraMulD A B) C = algebraMulD A (algebraMulD B C)
  /-- Unit is left identity -/
  one_mul : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    algebraMulD algebraOneD A = A
  /-- Unit is right identity -/
  mul_one : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    algebraMulD A algebraOneD = A
  /-- Adjoint is involutive: (A†)† = A -/
  adjoint_involutive : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    algebraAdjointD (algebraAdjointD A) = A
  /-- Adjoint reverses multiplication: (AB)† = B†A† -/
  adjoint_mul : ∀ {O : Set (SpaceTimePointD d)} (A B : LocalAlgebraD d O),
    algebraAdjointD (algebraMulD A B) = algebraMulD (algebraAdjointD B) (algebraAdjointD A)
  /-- Norm is non-negative -/
  norm_nonneg : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    algebraNormD A ≥ 0
  /-- C*-identity: ‖A†A‖ = ‖A‖² -/
  norm_cstar : ∀ {O : Set (SpaceTimePointD d)} (A : LocalAlgebraD d O),
    algebraNormD (algebraMulD (algebraAdjointD A) A) = (algebraNormD A)^2

/-- The local algebras satisfy the C*-algebra axioms -/
axiom localAlgebraAxiomsD {d : ℕ} : LocalAlgebraAxioms d

theorem algebraNormD_nonneg {d : ℕ} {O : Set (SpaceTimePointD d)}
    (A : LocalAlgebraD d O) : algebraNormD A ≥ 0 :=
  localAlgebraAxiomsD.norm_nonneg A

theorem algebraNormD_cstar {d : ℕ} {O : Set (SpaceTimePointD d)}
    (A : LocalAlgebraD d O) :
    algebraNormD (algebraMulD (algebraAdjointD A) A) = (algebraNormD A)^2 :=
  localAlgebraAxiomsD.norm_cstar A

-- Legacy 4D aliases for backward compatibility
abbrev LocalAlgebra (O : Set (SpaceTimePointD 4)) := LocalAlgebraD 4 O
noncomputable abbrev algebraMul {O : Set (SpaceTimePointD 4)} := @algebraMulD 4 O
noncomputable abbrev algebraAdd {O : Set (SpaceTimePointD 4)} := @algebraAddD 4 O
noncomputable abbrev algebraAdjoint {O : Set (SpaceTimePointD 4)} := @algebraAdjointD 4 O
noncomputable abbrev algebraInclusion := @algebraInclusionD 4

end ModularPhysics.Core.QFT.AQFT

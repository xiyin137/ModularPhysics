-- ModularPhysics/Core/QFT/AQFT/LocalAlgebras.lean
-- Local algebras of observables for Algebraic QFT (Haag-Kastler framework)
import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Data.Real.Basic

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime

/-- A point in d-dimensional spacetime -/
abbrev SpaceTimePointD (d : ℕ) := Fin d → ℝ

/-- C*-algebra of observables for a spacetime region in d dimensions

    In AQFT, each bounded open region O of spacetime is assigned a
    von Neumann algebra A(O) of observables localized in that region.

    Key properties:
    - Self-adjoint elements correspond to physical observables
    - Algebra operations encode the quantum structure
    - Localization captures the finite-speed-of-light constraint -/
axiom LocalAlgebraD (d : ℕ) : Set (SpaceTimePointD d) → Type _

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

/-- Norm is non-negative -/
axiom algebraNormD_nonneg {d : ℕ} {O : Set (SpaceTimePointD d)}
  (A : LocalAlgebraD d O) : algebraNormD A ≥ 0

/-- C*-identity: ‖A*A‖ = ‖A‖² -/
axiom algebraNormD_cstar {d : ℕ} {O : Set (SpaceTimePointD d)}
  (A : LocalAlgebraD d O) :
  algebraNormD (algebraMulD (algebraAdjointD A) A) = (algebraNormD A)^2

-- Legacy 4D aliases for backward compatibility
abbrev LocalAlgebra := LocalAlgebraD 4
noncomputable abbrev algebraMul {O : Set (SpaceTimePointD 4)} := @algebraMulD 4 O
noncomputable abbrev algebraAdd {O : Set (SpaceTimePointD 4)} := @algebraAddD 4 O
noncomputable abbrev algebraAdjoint {O : Set (SpaceTimePointD 4)} := @algebraAdjointD 4 O
noncomputable abbrev algebraInclusion := @algebraInclusionD 4

end ModularPhysics.Core.QFT.AQFT

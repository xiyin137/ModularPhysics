import ModularPhysics.PhysicsLogic.SpaceTime.Basic
import ModularPhysics.PhysicsLogic.SpaceTime.Metrics

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Classical field configuration: maps spacetime points to values -/
def ClassicalField (F : Type*) := SpaceTimePoint → F

/-- Scalar field -/
abbrev ScalarField := ClassicalField ℝ

/-- Complex scalar field -/
abbrev ComplexScalarField := ClassicalField ℂ

/-- Vector field (4-vector at each point) -/
abbrev VectorField := ClassicalField (Fin 4 → ℝ)

/-- Tensor field -/
def TensorField (m n : ℕ) := ClassicalField (Fin m → Fin n → ℝ)

/-- Structure for spinor field types -/
structure SpinorTypes where
  /-- Spinor field type -/
  SpinorField : Type*
  /-- Dirac spinor type -/
  DiracSpinor : Type*

/-- Structure for derivative operations on fields -/
structure FieldDerivatives (F : Type*) where
  /-- Partial derivative ∂_μ φ -/
  partialDerivative : ClassicalField F → Fin 4 → ClassicalField F
  /-- Covariant derivative ∇_μ (uses metric connection) -/
  covariantDerivative : SpacetimeMetric → ClassicalField F → Fin 4 → ClassicalField F
  /-- Lie derivative along vector field -/
  lieDerivative : VectorField → ClassicalField F → ClassicalField F

/-- Structure for scalar field differential operators -/
structure ScalarFieldOperators where
  /-- Field derivatives for scalars -/
  derivatives : FieldDerivatives ℝ
  /-- d'Alembertian operator □ = ∂_μ ∂^μ (flat spacetime) -/
  dalembertian : ScalarField → ScalarField
  /-- Laplacian in curved spacetime -/
  laplacian : SpacetimeMetric → ScalarField → ScalarField

/-- Structure for vector field differential operators -/
structure VectorFieldOperators where
  /-- Field derivatives for vectors -/
  derivatives : FieldDerivatives (Fin 4 → ℝ)
  /-- Exterior derivative -/
  exteriorDerivative : VectorField → TensorField 4 4

end ModularPhysics.Core.ClassicalFieldTheory

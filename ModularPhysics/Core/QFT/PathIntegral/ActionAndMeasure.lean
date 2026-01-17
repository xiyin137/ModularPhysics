import ModularPhysics.Core.QFT.PathIntegral.FieldConfigurations
import ModularPhysics.Core.QFT.PathIntegral.Supergeometry

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= ACTION FUNCTIONAL ============= -/

/-- Action functional S[φ] on field configurations -/
structure ActionFunctional (F : Type _) where
  eval : F → ℝ
  /-- Action is local -/
  locality : Prop
  /-- First variation gives equations of motion -/
  equations_of_motion : F → F → ℝ

/-- Euclidean action (bounded below, ensures convergence) -/
structure EuclideanAction (F : Type _) extends ActionFunctional F where
  bounded_below : ∃ (c : ℝ), ∀ φ : F, eval φ ≥ c

/-- Wick rotation: it → τ -/
axiom wickRotation {F : Type _} :
  ActionFunctional F → EuclideanAction F

/- ============= MEASURE ON FIELD SPACE ============= -/

/-- Formal measure Dφ (needs regularization to be well-defined!) -/
axiom FieldMeasure (F : Type _) : Type _

/-- Bosonic measure (translation invariant for linear theories) -/
axiom bosonicMeasure {M V : Type _}
  [LinearFieldSpace M V] : FieldMeasure (FieldConfig M V)

/-- Fermionic measure: uses Berezin integration
    Key property: sign change under exchange
    ∫ Dψ Dχ F[ψ,χ] = -∫ Dχ Dψ F[ψ,χ] -/
structure FermionicMeasure (F : Type _) (G : GrassmannAlgebra) where
  measure : FieldMeasure F
  berezin : BerezinIntegral G
  /-- Grassmann nature: sign change under exchange -/
  anticommuting : Prop

/-- Jacobian for change of variables
    Bosonic: ordinary determinant
    Fermionic: Berezinian (superdeterminant) -/
axiom jacobianDeterminant {F₁ F₂ : Type _} (f : F₁ → F₂) : ℂ

end ModularPhysics.Core.QFT.PathIntegral

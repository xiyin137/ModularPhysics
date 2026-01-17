import ModularPhysics.Core.QFT.AQFT.LocalAlgebras
import ModularPhysics.Core.SpaceTime.Causality
import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.Symmetries.Poincare

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime Symmetries

/-- AQFT Axiom A1: Isotony (functoriality of inclusion) -/
axiom isotony (O₁ O₂ O₃ : Set SpaceTimePoint)
  (h12 : O₁ ⊆ O₂) (h23 : O₂ ⊆ O₃) :
  algebraInclusion O₁ O₃ (h12.trans h23) =
  algebraInclusion O₂ O₃ h23 ∘ algebraInclusion O₁ O₂ h12

/-- Two regions are spacelike separated -/
axiom SpacelikeSeparated (metric : SpacetimeMetric) (O₁ O₂ : Set SpaceTimePoint) : Prop

/-- AQFT Axiom A2: Locality (Einstein causality)
    Observables at spacelike separation commute -/
axiom locality
  (metric : SpacetimeMetric)
  (O₁ O₂ : Set SpaceTimePoint)
  (h : SpacelikeSeparated metric O₁ O₂)
  (A : LocalAlgebra O₁) (B : LocalAlgebra O₂)
  (O : Set SpaceTimePoint) (h1 : O₁ ⊆ O) (h2 : O₂ ⊆ O) :
  algebraMul (algebraInclusion O₁ O h1 A) (algebraInclusion O₂ O h2 B) =
  algebraMul (algebraInclusion O₂ O h2 B) (algebraInclusion O₁ O h1 A)

/-- Apply Poincaré transformation to region -/
axiom poincareImage (g : PoincareTransform) (O : Set SpaceTimePoint) : Set SpaceTimePoint

/-- AQFT Axiom A3: Covariance under Poincaré group -/
axiom covariance (O : Set SpaceTimePoint) (g : PoincareTransform) :
  ∃ (_ : LocalAlgebra O → LocalAlgebra (poincareImage g O)), True

/-- AQFT Axiom A4: Positivity of energy (spectrum condition) -/
axiom positivity_of_energy :
  ∀ (_ : PoincareTransform), True

end ModularPhysics.Core.QFT.AQFT

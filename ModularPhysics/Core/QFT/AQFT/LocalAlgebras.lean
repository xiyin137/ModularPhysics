import ModularPhysics.Core.SpaceTime.Basic

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime

/-- C*-algebra of observables for a spacetime region -/
axiom LocalAlgebra : Set SpaceTimePoint → Type _

/-- Algebra multiplication -/
axiom algebraMul {O : Set SpaceTimePoint} :
  LocalAlgebra O → LocalAlgebra O → LocalAlgebra O

/-- Algebra addition -/
axiom algebraAdd {O : Set SpaceTimePoint} :
  LocalAlgebra O → LocalAlgebra O → LocalAlgebra O

/-- Adjoint operation (Hermitian conjugate) -/
axiom algebraAdjoint {O : Set SpaceTimePoint} :
  LocalAlgebra O → LocalAlgebra O

/-- Algebra inclusion for nested regions: O₁ ⊆ O₂ → A(O₁) ⊆ A(O₂) -/
axiom algebraInclusion (O₁ O₂ : Set SpaceTimePoint)
  (h : O₁ ⊆ O₂) :
  LocalAlgebra O₁ → LocalAlgebra O₂

end ModularPhysics.Core.QFT.AQFT

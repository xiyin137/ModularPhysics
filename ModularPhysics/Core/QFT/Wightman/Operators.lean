import ModularPhysics.Core.SpaceTime.Basic
import ModularPhysics.Core.Quantum

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum

/-- Quantum field operator Φ(x) acting on Hilbert space -/
axiom QuantumFieldOperator (H : Type _) [QuantumStateSpace H] : Type _

/-- Field operator acts on states at a spacetime point -/
axiom fieldAction {H : Type _} [QuantumStateSpace H] :
  QuantumFieldOperator H → SpaceTimePoint → (H → H)

/-- Vacuum state |0⟩ -/
axiom vacuum {H : Type _} [QuantumStateSpace H] : H

/-- Vacuum is normalized -/
axiom vacuum_normalized {H : Type _} [QuantumStateSpace H] :
  ‖@vacuum H _‖ = 1

/-- Hermitian adjoint of field operator -/
axiom fieldAdjoint {H : Type _} [QuantumStateSpace H] :
  QuantumFieldOperator H → QuantumFieldOperator H

/-- Reality condition: φ†(x) = φ(x) for real scalar fields -/
axiom reality_condition {H : Type _} [QuantumStateSpace H]
  (phi : QuantumFieldOperator H) :
  fieldAdjoint phi = phi

/-- Time-ordered product -/
axiom timeOrderedProduct {H : Type _} [QuantumStateSpace H] :
  QuantumFieldOperator H → QuantumFieldOperator H →
  SpaceTimePoint → SpaceTimePoint → QuantumFieldOperator H

end ModularPhysics.Core.QFT.Wightman

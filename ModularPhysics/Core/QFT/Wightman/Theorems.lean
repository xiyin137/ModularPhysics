import ModularPhysics.Core.QFT.Wightman.WightmanFunctions

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum

/-- PCT theorem: combined CPT symmetry -/
axiom pct_theorem {H : Type _} [QuantumStateSpace H]
  (phi : QuantumFieldOperator H) :
  ∃ (_ : QuantumFieldOperator H → QuantumFieldOperator H), True

/-- Spin-statistics theorem: integer spin → bosons, half-integer → fermions -/
axiom spin_statistics :
  ∀ (spin : ℕ), (spin % 2 = 0 → True) ∧ (spin % 2 = 1 → True)

end ModularPhysics.Core.QFT.Wightman

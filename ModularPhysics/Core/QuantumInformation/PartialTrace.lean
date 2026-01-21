import ModularPhysics.Core.Quantum

namespace ModularPhysics.Core.QuantumInformation

open Quantum

/-- Partial trace over second subsystem.
    Given a density operator on the tensor product space, trace out the second subsystem. -/
structure PartialTrace2 {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
    (T : TensorProductSpace H1 H2) where
  /-- The partial trace operation -/
  trace : DensityOperator T.carrier → DensityOperator H1

/-- Partial trace over first subsystem.
    Given a density operator on the tensor product space, trace out the first subsystem. -/
structure PartialTrace1 {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
    (T : TensorProductSpace H1 H2) where
  /-- The partial trace operation -/
  trace : DensityOperator T.carrier → DensityOperator H2

end ModularPhysics.Core.QuantumInformation

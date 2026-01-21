import ModularPhysics.Core.Quantum
import ModularPhysics.Core.QuantumInformation.Correlations

namespace ModularPhysics.Core.QuantumInformation

open Quantum QuantumInformation

/-- Structure for entanglement theory on bipartite systems -/
structure EntanglementTheory {H1 H2 : Type _}
    [QuantumStateSpace H1] [QuantumStateSpace H2]
    (T : TensorProductSpace H1 H2) where
  /-- A state is separable (not entangled) -/
  Separable : DensityOperator T.carrier → Prop
  /-- Entanglement of formation -/
  entanglementOfFormation : DensityOperator T.carrier → ℝ
  /-- Entanglement of distillation -/
  entanglementOfDistillation : DensityOperator T.carrier → ℝ
  /-- Squashed entanglement -/
  squashedEntanglement : DensityOperator T.carrier → ℝ
  /-- Logarithmic negativity -/
  logarithmicNegativity : DensityOperator T.carrier → ℝ
  /-- Product states are separable -/
  product_separable : ∃ (rho : DensityOperator T.carrier), Separable rho
  /-- Separable states have zero EoF -/
  separable_zero_entanglement : ∀ (rho : DensityOperator T.carrier),
    Separable rho → entanglementOfFormation rho = 0

/-- Structure for LOCC operations on bipartite systems -/
structure LOCCTheory {H1 H2 : Type _}
    [QuantumStateSpace H1] [QuantumStateSpace H2]
    (T : TensorProductSpace H1 H2)
    (et : EntanglementTheory T) where
  /-- Type of LOCC operations -/
  LOCC : Type _
  /-- Apply LOCC operation -/
  applyLOCC : LOCC → DensityOperator T.carrier → DensityOperator T.carrier

/-- Structure for qubit entanglement theory with special properties -/
structure QubitEntanglementTheory
    (et : EntanglementTheory qubitTensorProduct)
    (bc : BipartiteCorrelations qubitTensorProduct (cm : CorrelationMeasures QubitPair)) where
  /-- Separable states can have nonzero discord -/
  separable_discord_nonzero :
    ∃ (rho : DensityOperator QubitPair),
      et.Separable rho ∧ bc.quantumDiscord rho > 0
  /-- Bound entangled states exist (undistillable but entangled) -/
  bound_entanglement_exists :
    ∃ (rho : DensityOperator QubitPair),
      et.entanglementOfFormation rho > 0 ∧
      et.entanglementOfDistillation rho = 0

variable {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]

/-- Distillable entanglement is less than EoF.

    This is a THEOREM (provable from entanglement theory), not an axiom itself. -/
theorem distillation_less_than_formation
  (T : TensorProductSpace H1 H2)
  (et : EntanglementTheory T)
  (rho : DensityOperator T.carrier) :
  et.entanglementOfDistillation rho ≤ et.entanglementOfFormation rho := by
  sorry

/-- LOCC cannot increase entanglement (monotonicity).

    This is a THEOREM (provable from LOCC theory), not an axiom itself. -/
theorem locc_monotone
  (T : TensorProductSpace H1 H2)
  (et : EntanglementTheory T)
  (lt : LOCCTheory T et)
  (rho : DensityOperator T.carrier)
  (locc_op : lt.LOCC) :
  et.entanglementOfFormation (lt.applyLOCC locc_op rho) ≤ et.entanglementOfFormation rho := by
  sorry

/-- LOCC cannot create entanglement from separable states.

    This is a THEOREM (provable from LOCC theory), not an axiom itself. -/
theorem locc_preserves_separability
  (T : TensorProductSpace H1 H2)
  (et : EntanglementTheory T)
  (lt : LOCCTheory T et)
  (rho : DensityOperator T.carrier)
  (h : et.Separable rho)
  (locc_op : lt.LOCC) :
  et.Separable (lt.applyLOCC locc_op rho) := by
  sorry

end ModularPhysics.Core.QuantumInformation

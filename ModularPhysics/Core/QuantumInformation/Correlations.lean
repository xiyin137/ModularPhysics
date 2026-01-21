import ModularPhysics.Core.Quantum
import ModularPhysics.Core.QuantumInformation.Entropy

namespace ModularPhysics.Core.QuantumInformation

open Quantum

/-- Mutual information for a tensor product state. -/
axiom mutualInformation {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2]
  (T : TensorProductSpace H1 H2) :
  DensityOperator T.carrier → ℝ

/-- Mutual information is non-negative -/
axiom mutual_information_nonneg {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2]
  (T : TensorProductSpace H1 H2)
  (rho : DensityOperator T.carrier) :
  mutualInformation T rho ≥ 0

/-- Conditional mutual information for tripartite systems.
    Uses nested tensor products: HA ⊗ (HB ⊗ HC). -/
axiom conditionalMutualInformation {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
  (T_BC : TensorProductSpace HB HC)
  (T_A_BC : TensorProductSpace HA T_BC.carrier) :
  DensityOperator T_A_BC.carrier → ℝ

/-- Quantum CMI is non-negative (consequence of SSA) -/
axiom quantum_cmi_nonneg {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
  (T_BC : TensorProductSpace HB HC)
  (T_A_BC : TensorProductSpace HA T_BC.carrier)
  (rho : DensityOperator T_A_BC.carrier) :
  conditionalMutualInformation T_BC T_A_BC rho ≥ 0

/-- Monogamy inequality for mutual information -/
axiom monogamy_inequality {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
  (I_AB I_AC I_BC : ℝ) :
  I_AB + I_AC ≥ I_BC

/-- Quantum discord for a tensor product state. -/
axiom quantumDiscord {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2]
  (T : TensorProductSpace H1 H2) :
  DensityOperator T.carrier → ℝ

/-- Discord is non-negative -/
axiom discord_nonneg {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
  (T : TensorProductSpace H1 H2)
  (rho : DensityOperator T.carrier) :
  quantumDiscord T rho ≥ 0

/-- Discord bounded by mutual information -/
axiom discord_bound {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
  (T : TensorProductSpace H1 H2)
  (rho : DensityOperator T.carrier) :
  quantumDiscord T rho ≤ mutualInformation T rho

/-- Quantum fidelity -/
axiom fidelity {H : Type _} [QuantumStateSpace H] :
  DensityOperator H → DensityOperator H → ℝ

/-- Fidelity bounds -/
axiom fidelity_bounds {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  0 ≤ fidelity rho sigma ∧ fidelity rho sigma ≤ 1

/-- Fidelity is symmetric -/
axiom fidelity_symmetric {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  fidelity rho sigma = fidelity sigma rho

/-- Pure state fidelity is amplitude squared -/
axiom pure_fidelity {H : Type _} [QuantumStateSpace H] (psi phi : PureState H) :
  fidelity (pureToDensity psi) (pureToDensity phi) = bornRule psi phi

/-- Uhlmann's theorem: fidelity achieved by purifications.
    Takes a tensor product structure for the purifying system. -/
axiom uhlmann_theorem {H : Type _} [QuantumStateSpace H]
  (T : TensorProductSpace H H)
  (rho sigma : DensityOperator H) :
  ∃ (psi phi : PureState T.carrier),
    fidelity rho sigma = bornRule psi phi

/-- Trace distance -/
axiom traceDistance {H : Type _} [QuantumStateSpace H] :
  DensityOperator H → DensityOperator H → ℝ

/-- Trace distance bounds -/
axiom trace_distance_bounds {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  0 ≤ traceDistance rho sigma ∧ traceDistance rho sigma ≤ 1

/-- Trace distance is a metric -/
axiom trace_distance_triangle {H : Type _} [QuantumStateSpace H]
  (rho sigma tau : DensityOperator H) :
  traceDistance rho tau ≤ traceDistance rho sigma + traceDistance sigma tau

/-- Fuchs-van de Graaf inequalities -/
axiom fuchs_van_de_graaf_lower {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  1 - fidelity rho sigma ≤ traceDistance rho sigma

axiom fuchs_van_de_graaf_upper {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  traceDistance rho sigma ≤ Real.sqrt (1 - (fidelity rho sigma)^2)

end ModularPhysics.Core.QuantumInformation

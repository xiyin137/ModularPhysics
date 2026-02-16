import ModularPhysics.PhysicsLogic.ClassicalFieldTheory.Noether
import ModularPhysics.PhysicsLogic.SpaceTime.Metrics

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Structure for energy-momentum tensor and conservation -/
structure EnergyMomentumTheory (F : Type*) (actionTheory : ActionTheory F)
    (eom : EquationsOfMotion F actionTheory)
    (scalarOps : ScalarFieldOperators) where
  /-- Canonical energy-momentum tensor T^μν -/
  energyMomentumTensor :
    ClassicalField F → SpaceTimePoint → Fin 4 → Fin 4 → ℝ
  /-- Belinfante-Rosenfeld tensor (symmetric, gauge-invariant) -/
  belinfanteRosenfeld :
    ClassicalField F → SpaceTimePoint → Fin 4 → Fin 4 → ℝ
  /-- Total energy E = ∫ T⁰⁰ d³x -/
  totalEnergy : ClassicalField F → ℝ
  /-- Total momentum P^i = ∫ T⁰ⁱ d³x -/
  totalMomentum : ClassicalField F → Fin 3 → ℝ
  /-- Total angular momentum J^ij = ∫ (x^i T⁰ʲ - x^j T⁰ⁱ) d³x -/
  totalAngularMomentum : ClassicalField F → Fin 3 → ℝ
  /-- Energy-momentum conservation: ∂_μ T^μν = 0 (flat spacetime) -/
  energy_momentum_conservation : ∀ (phi : ClassicalField F)
      (_h : eom.eulerLagrange phi)
      (x : SpaceTimePoint) (nu : Fin 4),
    ∑ mu, scalarOps.derivatives.partialDerivative (fun y => energyMomentumTensor phi y mu nu) mu x = 0

/-- Structure for covariant energy-momentum conservation in curved spacetime -/
structure CurvedEnergyMomentumTheory (F : Type*) (actionTheory : ActionTheory F)
    (eom : EquationsOfMotion F actionTheory)
    (scalarOps : ScalarFieldOperators)
    (emt : EnergyMomentumTheory F actionTheory eom scalarOps) where
  /-- Covariant conservation in curved spacetime: ∇_μ T^μν = 0 -/
  covariant_energy_momentum_conservation :
    ∀ (metric : SpacetimeMetric) (phi : ClassicalField F)
      (x : SpaceTimePoint) (nu : Fin 4),
    ∑ mu, scalarOps.derivatives.covariantDerivative metric (fun y => emt.energyMomentumTensor phi y mu nu) mu x = 0

/-- Perfect fluid stress-energy tensor: T_μν = (ρ + p)u_μ u_ν + p g_μν -/
def perfectFluidStressEnergy (metric : SpacetimeMetric)
    (ρ p : SpaceTimePoint → ℝ)  -- energy density and pressure
    (u : SpaceTimePoint → Fin 4 → ℝ)  -- 4-velocity
    : TensorField 4 4 :=
  fun x μ ν => (ρ x + p x) * u x μ * u x ν + p x * metric.g x μ ν

end ModularPhysics.Core.ClassicalFieldTheory

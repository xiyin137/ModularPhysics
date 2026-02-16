import ModularPhysics.PhysicsLogic.ClassicalFieldTheory.EulerLagrange

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Structure for Noether's theorem and conserved currents -/
structure NoetherTheory (F : Type*) (actionTheory : ActionTheory F)
    (eom : EquationsOfMotion F actionTheory)
    (scalarOps : ScalarFieldOperators) where
  /-- Noether current j^μ associated with continuous symmetry -/
  noetherCurrent :
    (phi : ClassicalField F) →
    (symmetry : ClassicalField F → ClassicalField F) →
    SpaceTimePoint → Fin 4 → ℝ
  /-- Conserved charge Q = ∫ j⁰ d³x -/
  conservedCharge :
    (phi : ClassicalField F) →
    (symmetry : ClassicalField F → ClassicalField F) → ℝ
  /-- Noether's theorem: continuous symmetry → conserved current
      If δL = ∂_μ K^μ under symmetry transformation, then
      ∂_μ j^μ = 0 (on-shell) -/
  noether_theorem : ∀ (phi : ClassicalField F)
    (symmetry : ClassicalField F → ClassicalField F)
    (h : eom.eulerLagrange phi)
    (x : SpaceTimePoint),
    ∑ mu, scalarOps.derivatives.partialDerivative (fun y => noetherCurrent phi symmetry y mu) mu x = 0
  /-- Time translation → energy conservation -/
  energy_from_time_translation : ∀ (phi : ClassicalField F) (x : SpaceTimePoint),
    ∃ (time_translation : ClassicalField F → ClassicalField F),
      conservedCharge phi time_translation = noetherCurrent phi time_translation x 0
  /-- Spatial translation → momentum conservation -/
  momentum_from_spatial_translation : ∀ (phi : ClassicalField F) (i : Fin 3) (x : SpaceTimePoint),
    ∃ (spatial_translation : ClassicalField F → ClassicalField F),
      conservedCharge phi spatial_translation = noetherCurrent phi spatial_translation x i.succ

end ModularPhysics.Core.ClassicalFieldTheory

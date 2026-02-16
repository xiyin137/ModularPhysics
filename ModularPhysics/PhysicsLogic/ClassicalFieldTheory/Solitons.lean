import ModularPhysics.PhysicsLogic.ClassicalFieldTheory.Scalar
import ModularPhysics.PhysicsLogic.ClassicalFieldTheory.YangMills

namespace ModularPhysics.Core.ClassicalFieldTheory

/-- Structure for soliton solutions in field theory -/
structure SolitonTheory (F : Type*) (at : ActionTheory F)
    (emt : EnergyMomentumTheory F at (eom : EquationsOfMotion F at) (fd : FieldDerivatives F)) where
  /-- Topological charge for solitons -/
  solitonCharge : ClassicalField F → ℤ
  /-- Soliton stability from topology -/
  soliton_stable : ∀ (phi : ClassicalField F) (h : solitonCharge phi ≠ 0),
    ∃ (E_min : ℝ), ∀ (psi : ClassicalField F),
      solitonCharge psi = solitonCharge phi → emt.totalEnergy psi ≥ E_min

/-- Structure for scalar solitons -/
structure ScalarSolitons where
  /-- Kink solution (φ⁴ in 1+1D) -/
  kinkSolution : ScalarField
  /-- Domain wall -/
  domainWall : ScalarField
  /-- Cosmic string -/
  cosmicString : ScalarField

/-- Structure for gauge solitons -/
structure GaugeSolitons (ymt : YangMillsTheory) where
  /-- Vortex solution (Abrikosov-Nielsen-Olesen) -/
  vortexSolution : ComplexScalarField × EMPotential
  /-- Monopole solution ('t Hooft-Polyakov) -/
  magneticMonopole : ymt.YMField
  /-- Skyrmion -/
  skyrmion : VectorField

end ModularPhysics.Core.ClassicalFieldTheory

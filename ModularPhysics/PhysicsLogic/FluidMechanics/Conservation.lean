import ModularPhysics.PhysicsLogic.FluidMechanics.Basic

namespace ModularPhysics.Core.FluidMechanics

set_option autoImplicit false

/- ============= CONSERVATION LAWS ============= -/

variable (ops : DifferentialOperators)
variable (md : MaterialDerivative ops)

/-- Continuity equation (mass conservation): Dρ/Dt + ρ∇·v = 0 -/
def satisfiesContinuity (ρ : DensityField) (v : VelocityField) : Prop :=
  ∀ x t, md.materialDerivativeScalar v ρ x t + ρ x t * ops.divergence v x t = 0

/-- Incompressibility condition: ∇·v = 0 -/
def isIncompressible (v : VelocityField) : Prop :=
  ∀ x t, ops.divergence v x t = 0

/-- Structure for conservation laws -/
structure ConservationLaws (ops : DifferentialOperators) (md : MaterialDerivative ops) where
  /-- For incompressible flow, continuity implies Dρ/Dt = 0 -/
  incompressible_implies_constant_density : ∀ (v : VelocityField) (ρ : DensityField),
    isIncompressible ops v →
    satisfiesContinuity ops md ρ v →
    (∀ x t, md.materialDerivativeScalar v ρ x t = 0)

/-- Momentum conservation (Cauchy equation): ρDv/Dt = ∇·σ + f -/
def satisfiesMomentumEquation
  (ρ : DensityField)
  (v : VelocityField)
  (σ : StressTensor)
  (f : VectorField3D) : Prop :=
  ∀ x t i, ρ x t * md.materialDerivativeVector v v x t i =
           ops.divergenceTensor σ x t i + f x t i

/-- Energy equation: ρ De/Dt = -∇·q + σ:∇v + Q -/
def satisfiesEnergyEquation
  (ρ : DensityField)
  (e : ScalarField)
  (v : VelocityField)
  (q : VectorField3D)
  (σ : StressTensor)
  (Q : ScalarField) : Prop :=
  ∀ x t, ρ x t * md.materialDerivativeScalar v e x t =
         -(ops.divergence q x t) +
         (∑ i : Fin 3, ∑ j : Fin 3, σ x t i j * ops.gradient (fun y s => v y s j) x t i) +
         Q x t

end ModularPhysics.Core.FluidMechanics

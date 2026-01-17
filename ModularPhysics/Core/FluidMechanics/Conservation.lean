import ModularPhysics.Core.FluidMechanics.Basic

namespace ModularPhysics.Core.FluidMechanics

set_option autoImplicit false

/- ============= CONSERVATION LAWS ============= -/

/-- Continuity equation (mass conservation): Dρ/Dt + ρ∇·v = 0 -/
def satisfiesContinuity (ρ : DensityField) (v : VelocityField) : Prop :=
  ∀ x t, materialDerivativeScalar v ρ x t + ρ x t * divergence v x t = 0

/-- Incompressibility condition: ∇·v = 0 -/
def isIncompressible (v : VelocityField) : Prop :=
  ∀ x t, divergence v x t = 0

/-- For incompressible flow, continuity implies Dρ/Dt = 0 -/
axiom incompressible_implies_constant_density (v : VelocityField) (ρ : DensityField) :
  isIncompressible v →
  satisfiesContinuity ρ v →
  (∀ x t, materialDerivativeScalar v ρ x t = 0)

/-- Momentum conservation (Cauchy equation): ρDv/Dt = ∇·σ + f -/
def satisfiesMomentumEquation
  (ρ : DensityField)
  (v : VelocityField)
  (σ : StressTensor)
  (f : VectorField3D) : Prop :=
  ∀ x t i, ρ x t * materialDerivativeVector v v x t i =
           divergenceTensor σ x t i + f x t i

/-- Energy equation: ρ De/Dt = -∇·q + σ:∇v + Q -/
def satisfiesEnergyEquation
  (ρ : DensityField)
  (e : ScalarField)
  (v : VelocityField)
  (q : VectorField3D)
  (σ : StressTensor)
  (Q : ScalarField) : Prop :=
  ∀ x t, ρ x t * materialDerivativeScalar v e x t =
         -(divergence q x t) +
         (∑ i : Fin 3, ∑ j : Fin 3, σ x t i j * gradient (fun y s => v y s j) x t i) +
         Q x t

end ModularPhysics.Core.FluidMechanics

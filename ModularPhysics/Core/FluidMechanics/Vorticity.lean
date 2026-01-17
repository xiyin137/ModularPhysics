import ModularPhysics.Core.FluidMechanics.Basic
import ModularPhysics.Core.FluidMechanics.Conservation

namespace ModularPhysics.Core.FluidMechanics

set_option autoImplicit false

/- ============= VORTICITY DYNAMICS ============= -/

/-- Vorticity transport for incompressible flow: Dω/Dt = ω·∇v + ν∇²ω -/
def vorticityTransportEquation
  (v : VelocityField)
  (ν : ℝ) : Prop :=
  isIncompressible v ∧
  let ω := vorticity v
  ∀ x t i, materialDerivativeVector v ω x t i =
           (∑ j : Fin 3, ω x t j * gradient (fun y s => v y s i) x t j) +
           ν * vectorLaplacian ω x t i

end ModularPhysics.Core.FluidMechanics

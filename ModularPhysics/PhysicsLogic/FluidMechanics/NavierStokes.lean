import ModularPhysics.PhysicsLogic.FluidMechanics.Basic
import ModularPhysics.PhysicsLogic.FluidMechanics.Conservation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ModularPhysics.Core.FluidMechanics

set_option autoImplicit false

/- ============= NAVIER-STOKES EQUATIONS ============= -/

variable (ops : DifferentialOperators)
variable (md : MaterialDerivative ops)

/-- Incompressible Navier-Stokes: ∇·v = 0, Dv/Dt = -(1/ρ)∇p + ν∇²v + f -/
structure NavierStokesIncompressible
  (ρ : ℝ)
  (ν : ℝ)
  (v : VelocityField)
  (p : PressureField)
  (f : VectorField3D) : Prop where
  incompressibility : isIncompressible ops v
  momentum : ∀ x t i,
    md.materialDerivativeVector v v x t i =
    -(1/ρ) * ops.gradient p x t i +
    ν * ops.vectorLaplacian v x t i +
    f x t i

/-- Compressible Navier-Stokes equations -/
structure NavierStokesCompressible
  (cr : ConstitutiveRelations ops)
  (ρ : DensityField)
  (v : VelocityField)
  (p : PressureField)
  (T : TemperatureField)
  (e : ScalarField)
  (μ : ℝ)
  (lam : ℝ)
  (k : ℝ)
  (f : VectorField3D)
  (Q : ScalarField) : Prop where
  continuity : satisfiesContinuity ops md ρ v
  momentum : satisfiesMomentumEquation ops md ρ v (newtonianStressTensor cr p v μ lam) f
  energy : satisfiesEnergyEquation ops md ρ e v (fourierHeatFlux ops k T)
           (newtonianStressTensor cr p v μ lam) Q
  eos : p = cr.equationOfState ρ T

/- ============= EXACT SOLUTIONS ============= -/

/-- Taylor-Green vortex: prototype for studying transition to turbulence -/
noncomputable def taylorGreenVortex (A ν : ℝ) : VelocityField :=
  fun x t i =>
    match i with
    | 0 => A * Real.sin (x 0) * Real.cos (x 1) * Real.cos (x 2) * Real.exp (-3 * ν * t)
    | 1 => -A * Real.cos (x 0) * Real.sin (x 1) * Real.cos (x 2) * Real.exp (-3 * ν * t)
    | 2 => 0

/-- Structure for exact Navier-Stokes solutions -/
structure ExactNSSolutions (ops : DifferentialOperators) (md : MaterialDerivative ops) where
  /-- Taylor-Green vortex is incompressible -/
  taylor_green_incompressible : ∀ (A ν : ℝ),
    isIncompressible ops (taylorGreenVortex A ν)
  /-- Taylor-Green vortex satisfies Navier-Stokes (with zero forcing) -/
  taylor_green_navier_stokes : ∀ (A ν ρ : ℝ),
    ν > 0 → ρ > 0 →
    ∃ (p : PressureField),
      NavierStokesIncompressible ops md ρ ν (taylorGreenVortex A ν) p (fun _ _ _ => 0)

end ModularPhysics.Core.FluidMechanics

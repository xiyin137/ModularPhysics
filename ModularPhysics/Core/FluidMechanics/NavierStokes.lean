import ModularPhysics.Core.FluidMechanics.Basic
import ModularPhysics.Core.FluidMechanics.Conservation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ModularPhysics.Core.FluidMechanics

set_option autoImplicit false

/- ============= NAVIER-STOKES EQUATIONS ============= -/

/-- Incompressible Navier-Stokes: ∇·v = 0, Dv/Dt = -(1/ρ)∇p + ν∇²v + f -/
structure NavierStokesIncompressible
  (ρ : ℝ)
  (ν : ℝ)
  (v : VelocityField)
  (p : PressureField)
  (f : VectorField3D) : Prop where
  incompressibility : isIncompressible v
  momentum : ∀ x t i,
    materialDerivativeVector v v x t i =
    -(1/ρ) * gradient p x t i +
    ν * vectorLaplacian v x t i +
    f x t i

/-- Compressible Navier-Stokes equations -/
structure NavierStokesCompressible
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
  continuity : satisfiesContinuity ρ v
  momentum : satisfiesMomentumEquation ρ v (newtonianStressTensor p v μ lam) f
  energy : satisfiesEnergyEquation ρ e v (fourierHeatFlux k T)
           (newtonianStressTensor p v μ lam) Q
  eos : p = equationOfState ρ T

/- ============= EXACT SOLUTIONS ============= -/

/-- Taylor-Green vortex: prototype for studying transition to turbulence -/
noncomputable def taylorGreenVortex (A ν : ℝ) : VelocityField :=
  fun x t i =>
    match i with
    | 0 => A * Real.sin (x 0) * Real.cos (x 1) * Real.cos (x 2) * Real.exp (-3 * ν * t)
    | 1 => -A * Real.cos (x 0) * Real.sin (x 1) * Real.cos (x 2) * Real.exp (-3 * ν * t)
    | 2 => 0

/-- Taylor-Green vortex is incompressible -/
axiom taylor_green_incompressible (A ν : ℝ) :
  isIncompressible (taylorGreenVortex A ν)

/-- Taylor-Green vortex satisfies Navier-Stokes (with zero forcing) -/
axiom taylor_green_navier_stokes (A ν ρ : ℝ) :
  ν > 0 → ρ > 0 →
  ∃ (p : PressureField),
    NavierStokesIncompressible ρ ν (taylorGreenVortex A ν) p (fun _ _ _ => 0)

end ModularPhysics.Core.FluidMechanics

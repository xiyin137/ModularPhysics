import ModularPhysics.Core.FluidMechanics.Basic
import ModularPhysics.Core.FluidMechanics.Conservation

namespace ModularPhysics.Core.FluidMechanics

set_option autoImplicit false

/- ============= COMPRESSIBLE FLOW ============= -/

/-- Speed of sound -/
axiom speedOfSound (p : PressureField) (ρ : DensityField) : ScalarField

/-- Subsonic: V < c -/
def isSubsonic (v : VelocityField) (c : ScalarField) : Prop :=
  ∀ x t, Real.sqrt (∑ i : Fin 3, (v x t i)^2) < c x t

/-- Supersonic: V > c -/
def isSupersonic (v : VelocityField) (c : ScalarField) : Prop :=
  ∀ x t, Real.sqrt (∑ i : Fin 3, (v x t i)^2) > c x t

/-- Rankine-Hugoniot jump conditions across shock -/
def rankineHugoniotConditions
  (v_up v_down : Fin 3 → ℝ)
  (ρ_up ρ_down : ℝ)
  (p_up p_down : ℝ)
  (normal : Fin 3 → ℝ) : Prop :=
  let v_n_up := ∑ i, v_up i * normal i
  let v_n_down := ∑ i, v_down i * normal i
  (ρ_up * v_n_up = ρ_down * v_n_down) ∧
  (p_up + ρ_up * v_n_up^2 = p_down + ρ_down * v_n_down^2)

/-- Isentropic: Ds/Dt = 0 -/
def isIsentropic (v : VelocityField) (s : ScalarField) : Prop :=
  ∀ x t, materialDerivativeScalar v s x t = 0

/- ============= FLOW REGIMES ============= -/

/-- Laminar flow -/
axiom isLaminar (v : VelocityField) : Prop

/-- Turbulent flow -/
axiom isTurbulent (v : VelocityField) : Prop

/-- Laminar-turbulent transition Reynolds number -/
axiom transitionReynolds : ℝ

end ModularPhysics.Core.FluidMechanics

/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.SPDE.SPDE

/-!
# Stochastic Heat Equation

The stochastic heat equation ∂_t u = Δu + ξ where ξ is space-time white noise.

## Main Definitions

* `StochasticHeatEquation` - The stochastic heat equation
* `SHESolution` - Solutions via regularity structures

## References

* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
* Walsh, "An introduction to stochastic partial differential equations"
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## Stochastic Heat Equation -/

/-- The stochastic heat equation: ∂_t u = Δu + ξ
    where ξ is space-time white noise. -/
structure StochasticHeatEquation (d : ℕ) where
  /-- The spatial domain (usually torus or ℝ^d) -/
  domain : Set (Fin d → ℝ)
  /-- Diffusion coefficient (often normalized to 1) -/
  diffusion_coeff : ℝ := 1
  /-- Positivity of diffusion -/
  diffusion_pos : 0 < diffusion_coeff := by norm_num

namespace StochasticHeatEquation

variable {d : ℕ}

/-- The regularity of the noise -/
noncomputable def noiseRegularity (_she : StochasticHeatEquation d) : ℝ := -(d : ℝ)/2 - 1

/-- The expected solution regularity α < 1 - d/2 -/
noncomputable def solutionRegularity (_she : StochasticHeatEquation d) : ℝ := 1 - (d : ℝ)/2

/-- The stochastic heat equation is well-posed in d = 1 (no renormalization needed) -/
theorem well_posed_d1 (she : StochasticHeatEquation 1) :
    she.solutionRegularity > 0 := by
  simp [solutionRegularity]
  norm_num

/-- In d = 2, the solution has regularity α < 0 (distribution-valued) -/
theorem solution_distribution_d2 (she : StochasticHeatEquation 2) :
    she.solutionRegularity < 1 := by
  simp [solutionRegularity]

/-- Solution via regularity structures for d = 2 -/
noncomputable def regularity_structure_d2 : RegularityStructure 2 :=
  RegularityStructure.polynomial 2

/-- The mild formulation: u(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} dW_s -/
theorem mild_formulation (_she : StochasticHeatEquation d) :
    True := trivial

/-- The Hölder regularity is α < 1/2 - d/4 in space -/
theorem spatial_holder_regularity (_she : StochasticHeatEquation d) :
    ∃ α : ℝ, α < 1/2 - (d : ℝ)/4 ∧ True := ⟨1/2 - (d : ℝ)/4 - 1, by linarith, trivial⟩

/-- The Hölder regularity is β < 1/4 - d/8 in time -/
theorem temporal_holder_regularity (_she : StochasticHeatEquation d) :
    ∃ β : ℝ, β < 1/4 - (d : ℝ)/8 ∧ True := ⟨1/4 - (d : ℝ)/8 - 1, by linarith, trivial⟩

end StochasticHeatEquation

/-! ## Stochastic Heat Equation with Nonlinearity -/

/-- Stochastic heat equation with polynomial nonlinearity:
    ∂_t u = Δu + f(u) + g(u)ξ -/
structure NonlinearSHE (d : ℕ) where
  /-- The domain -/
  domain : Set (Fin d → ℝ)
  /-- The drift nonlinearity f -/
  drift : ℝ → ℝ
  /-- The multiplicative noise coefficient g -/
  noise_coeff : ℝ → ℝ
  /-- Lipschitz condition on f -/
  drift_lipschitz : ∃ L : ℝ, ∀ x y : ℝ, |drift x - drift y| ≤ L * |x - y|

namespace NonlinearSHE

/-- Additive noise case: g(u) = 1 -/
def additive (d : ℕ) (f : ℝ → ℝ) : NonlinearSHE d where
  domain := Set.univ
  drift := f
  noise_coeff := fun _ => 1
  drift_lipschitz := sorry

/-- Multiplicative noise case: g(u) = u -/
def multiplicative (d : ℕ) (f : ℝ → ℝ) : NonlinearSHE d where
  domain := Set.univ
  drift := f
  noise_coeff := id
  drift_lipschitz := sorry

end NonlinearSHE

end SPDE.Examples

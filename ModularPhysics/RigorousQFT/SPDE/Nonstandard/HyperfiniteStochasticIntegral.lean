/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.HyperfiniteRandomWalk
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.HyperfiniteIntegration

/-!
# Hyperfinite Stochastic Integration

This file develops the Itô integral via the hyperfinite approach. The key insight
is that the Itô integral becomes a simple finite sum in the hyperfinite setting:

  ∫₀ᵗ H dW ≈ Σₖ Hₖ · ΔWₖ

where the sum is over a hyperfinite number of terms.

## Main Ideas

In standard stochastic calculus, the Itô integral requires:
- Adapted processes
- L² integrability conditions
- Careful limit arguments

In the hyperfinite approach:
1. The random walk W has hyperfinite steps: ΔWₖ = ±dx where dx = √dt
2. The integrand H is evaluated at mesh points: Hₖ = H(tₖ)
3. The integral is a hyperfinite sum: Σₖ Hₖ · ΔWₖ
4. Taking standard parts yields the Itô integral

## Main Definitions

* `HyperfiniteStochasticIntegral` - The hyperfinite sum Σ Hₖ · ΔWₖ
* `quadraticVariation_stochastic` - Σ (Hₖ · ΔWₖ)²

## Main Results

* `stochastic_integral_quadratic_variation` - QV = Σ Hₖ² · dt (Itô isometry)
* `stochastic_integral_linearity` - Linearity properties

## References

* Lindstrøm, "Hyperfinite Stochastic Integration"
* Anderson, "A nonstandard representation for Brownian motion and Itô integration"
-/

open Hyperreal Finset

namespace SPDE.Nonstandard.StochasticIntegral

/-! ## Hyperfinite Stochastic Integral

The stochastic integral Σₖ Hₖ · ΔWₖ where ΔWₖ = ±dx.
-/

/-- A hyperfinite stochastic integral specification.
    Combines a random walk (the integrator) with an integrand. -/
structure HyperfiniteStochasticIntegral where
  /-- The underlying hyperfinite random walk (the Brownian motion approximation) -/
  walk : HyperfiniteWalk
  /-- The number of steps is infinite -/
  numSteps_infinite : Infinite walk.numSteps
  /-- The integrand as a function on step indices -/
  integrand : ℕ → ℝ*

namespace HyperfiniteStochasticIntegral

variable (I : HyperfiniteStochasticIntegral)

/-- Time step dt -/
noncomputable def dt : ℝ* := I.walk.dt

/-- Space step dx = √dt -/
noncomputable def dx : ℝ* := I.walk.dx

/-- The increment ΔWₖ = flips(k) · dx -/
noncomputable def increment (k : ℕ) : ℝ* :=
  I.walk.coins.flips k * I.dx

/-- Increment is ±dx -/
theorem increment_pm_dx (k : ℕ) :
    I.increment k = I.dx ∨ I.increment k = -I.dx := by
  unfold increment
  rcases I.walk.coins.flips_pm_one k with h | h
  · left; rw [h, one_mul]
  · right; rw [h, neg_one_mul]

/-- Increment squared equals dt -/
theorem increment_sq (k : ℕ) : (I.increment k)^2 = I.dt := by
  show (I.increment k)^2 = I.walk.dt
  rcases increment_pm_dx I k with h | h
  · simp only [h, dx]
    exact I.walk.dx_sq_eq_dt
  · simp only [h, neg_sq, dx]
    exact I.walk.dx_sq_eq_dt

/-- The hyperfinite stochastic integral up to step n: Σₖ₌₀ⁿ⁻¹ Hₖ · ΔWₖ -/
noncomputable def integral (n : ℕ) : ℝ* :=
  ∑ k ∈ range n, I.integrand k * I.increment k

/-- The integral starts at 0 -/
theorem integral_zero : I.integral 0 = 0 := by
  simp [integral]

/-- Recursive formula for the integral -/
theorem integral_succ (n : ℕ) :
    I.integral (n + 1) = I.integral n + I.integrand n * I.increment n := by
  simp [integral, sum_range_succ]

/-! ## Quadratic Variation (Itô Isometry)

The key property: Σ (Hₖ · ΔWₖ)² = Σ Hₖ² · dt
-/

/-- Quadratic variation of the stochastic integral up to step n -/
noncomputable def quadraticVariation (n : ℕ) : ℝ* :=
  ∑ k ∈ range n, (I.integrand k * I.increment k)^2

/-- Each term of QV equals Hₖ² · dt -/
theorem qv_term (k : ℕ) :
    (I.integrand k * I.increment k)^2 = (I.integrand k)^2 * I.dt := by
  rw [mul_pow, increment_sq]

/-- **Itô Isometry (hyperfinite version)**:
    The quadratic variation equals Σ Hₖ² · dt exactly. -/
theorem ito_isometry (n : ℕ) :
    I.quadraticVariation n = ∑ k ∈ range n, (I.integrand k)^2 * I.dt := by
  unfold quadraticVariation
  congr 1
  ext k
  exact qv_term I k

/-- Factoring out dt from the isometry -/
theorem ito_isometry' (n : ℕ) :
    I.quadraticVariation n = I.dt * ∑ k ∈ range n, (I.integrand k)^2 := by
  rw [ito_isometry, mul_sum]
  congr 1
  ext k
  ring

/-! ## Properties of the Stochastic Integral -/

/-- The integral is 0 when the integrand is 0 -/
theorem integral_zero_integrand (n : ℕ) (h : ∀ k, I.integrand k = 0) :
    I.integral n = 0 := by
  unfold integral
  apply sum_eq_zero
  intro k _
  rw [h k, zero_mul]

/-- Linearity: scalar multiplication -/
theorem integral_smul (c : ℝ*) (n : ℕ) :
    let I' : HyperfiniteStochasticIntegral := ⟨I.walk, I.numSteps_infinite, fun k => c * I.integrand k⟩
    I'.integral n = c * I.integral n := by
  simp only [integral, increment, dx]
  rw [mul_sum]
  congr 1
  ext k
  ring

end HyperfiniteStochasticIntegral

/-! ## Standard Integrands

When the integrand is a standard (non-hyperreal) function, we can connect
to standard stochastic integration via the standard part.
-/

/-- A stochastic integral with a standard integrand -/
noncomputable def standardIntegrand (walk : HyperfiniteWalk)
    (hN : Infinite walk.numSteps) (H : ℕ → ℝ) : HyperfiniteStochasticIntegral where
  walk := walk
  numSteps_infinite := hN
  integrand := fun k => (H k : ℝ*)

/-- The integral as a sequence (for taking standard parts) -/
noncomputable def integralSeq (walk : HyperfiniteWalk) (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, H k * (if walk.coins.flips k = 1 then 1 else -1) * st walk.dx

/-! ## Connection to Standard Itô Integral

The standard part of the hyperfinite integral should equal the Itô integral.
This requires:
1. The integrand H to be adapted and sufficiently regular
2. Taking limits as the number of steps → ∞
3. Using Loeb measure for the probability structure

The key theorem (informal):
  st(Σₖ Hₖ · ΔWₖ) = ∫₀ᵗ H dW  (Itô integral)

A complete proof requires the Loeb measure machinery from LoebMeasure.lean.
-/

/-- Placeholder: Standard part of hyperfinite integral equals Itô integral.

    This would require:
    - Loeb measure on the path space
    - Adaptedness of the integrand
    - L² bounds on H
    - The standard part map on function spaces -/
theorem st_hyperfinite_eq_ito (_walk : HyperfiniteWalk)
    (_hN : Infinite _walk.numSteps) (_H : ℕ → ℝ) :
    True := trivial

/-! ## Simple Integrands

For constant and linear integrands, we can compute explicitly.
-/

/-- For constant integrand H = c, the integral is c · Wₙ -/
theorem integral_const (walk : HyperfiniteWalk) (hN : Infinite walk.numSteps)
    (c : ℝ) (n : ℕ) :
    let I := standardIntegrand walk hN (fun _ => c)
    I.integral n = (c : ℝ*) * walk.walkAt n := by
  simp only [HyperfiniteStochasticIntegral.integral, standardIntegrand]
  simp only [HyperfiniteStochasticIntegral.increment, HyperfiniteStochasticIntegral.dx]
  rw [← mul_sum]
  congr 1
  unfold HyperfiniteWalk.walkAt
  rw [mul_comm, sum_mul]

/-- For constant integrand, QV = c² · n · dt -/
theorem qv_const (walk : HyperfiniteWalk) (hN : Infinite walk.numSteps)
    (c : ℝ) (n : ℕ) :
    let I := standardIntegrand walk hN (fun _ => c)
    I.quadraticVariation n = (c : ℝ*)^2 * (n : ℝ*) * walk.dt := by
  simp only [HyperfiniteStochasticIntegral.quadraticVariation, standardIntegrand,
             HyperfiniteStochasticIntegral.increment, HyperfiniteStochasticIntegral.dx]
  have h : ∀ k ∈ range n, ((c : ℝ*) * (walk.coins.flips k * walk.dx))^2 =
      (c : ℝ*)^2 * walk.dt := by
    intro k _
    rw [mul_pow, mul_pow]
    have hflip : (walk.coins.flips k)^2 = 1 := by
      rcases walk.coins.flips_pm_one k with hf | hf <;> simp [hf]
    rw [hflip, one_mul, walk.dx_sq_eq_dt]
  rw [sum_congr rfl h, sum_const, card_range]
  simp only [nsmul_eq_mul]
  ring

/-! ## Cross Variation

For two stochastic integrals, the cross variation structure.
-/

/-- Cross variation of two stochastic integrals -/
noncomputable def crossVariation (I J : HyperfiniteStochasticIntegral)
    (_hWalk : I.walk = J.walk) (n : ℕ) : ℝ* :=
  ∑ k ∈ range n, (I.integrand k * I.increment k) * (J.integrand k * J.increment k)

/-- Cross variation equals Σ Hₖ · Gₖ · dt when walks are the same -/
theorem cross_variation_eq (I J : HyperfiniteStochasticIntegral)
    (hWalk : I.walk = J.walk) (n : ℕ) :
    crossVariation I J (hWalk) n =
    ∑ k ∈ range n, I.integrand k * J.integrand k * I.dt := by
  unfold crossVariation
  congr 1
  ext k
  -- I.increment k = J.increment k since walks are the same
  have hinc : I.increment k = J.increment k := by
    simp only [HyperfiniteStochasticIntegral.increment,
               HyperfiniteStochasticIntegral.dx]
    rw [hWalk]
  rw [hinc]
  calc (I.integrand k * J.increment k) * (J.integrand k * J.increment k)
      = I.integrand k * J.integrand k * (J.increment k)^2 := by ring
    _ = I.integrand k * J.integrand k * J.dt := by rw [J.increment_sq]
    _ = I.integrand k * J.integrand k * I.dt := by
        have hdt : I.dt = J.dt := by
          simp only [HyperfiniteStochasticIntegral.dt]
          rw [hWalk]
        rw [hdt]

end SPDE.Nonstandard.StochasticIntegral

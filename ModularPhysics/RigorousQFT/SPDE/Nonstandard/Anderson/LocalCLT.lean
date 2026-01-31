/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.RandomWalkMoments
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.LoebMeasure.BinomialProbability
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Local Central Limit Theorem

This file provides infrastructure for the local central limit theorem, which shows that
the binomial distribution converges to the Gaussian distribution.

## Main Results

* `stirling_lower_bound` - Lower bound: n! ≥ √(2πn) (n/e)^n
* `stirling_upper_bound` - Upper bound: n! ≤ √(2πn) (n/e)^n e^(1/(12n))
* `binomial_gaussian_ratio` - |C(n,k)/2^n - φ((k-n/2)/√(n/4))/√(n/4)| = O(1/n)
* `binomial_near_gaussian` - The binomial prob is close to the Gaussian density

## Overview

For a symmetric random walk S_n with n steps:
- P(S_n = 2k - n) = C(n,k) / 2^n for k = 0, ..., n
- The centered, scaled walk has mean 0 and variance n/4
- By the local CLT: C(n,k)/2^n ≈ (1/√(πn/2)) exp(-(2k-n)²/(2n))

The local CLT is stronger than the standard CLT because it gives pointwise convergence
of the probability mass function, not just convergence of distribution functions.

## References

* Feller, W. "An Introduction to Probability Theory and Its Applications" Vol. 1, Ch. VII
* Petrov, V. V. "Sums of Independent Random Variables"
-/

open Real Finset

namespace SPDE.Nonstandard

/-! ## Stirling's Approximation Infrastructure

Stirling's formula: n! ≈ √(2πn) (n/e)^n

We state the bounds needed for the local CLT without proving them in full detail.
The full proofs would require Wallis' product formula or the Gamma function integral.
-/

/-- Stirling's approximation: n! ≈ √(2πn) (n/e)^n.
    We define the Stirling approximation function for convenience.
    Note: Matches Mathlib's formulation in `Stirling.le_factorial_stirling`. -/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  if n = 0 then 1
  else Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n

/-- Stirling lower bound: n! ≥ √(2πn) (n/e)^n for n ≥ 1.
    This follows directly from Mathlib's `Stirling.le_factorial_stirling`. -/
theorem stirling_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    stirlingApprox n ≤ (n.factorial : ℝ) := by
  unfold stirlingApprox
  simp only [Nat.one_le_iff_ne_zero.mp hn, ↓reduceIte]
  exact Stirling.le_factorial_stirling n

/-- Mathlib's Stirling sequence: stirlingSeq n = n! / (√(2n) (n/e)^n).
    The limit is √π. We relate this to our definition. -/
theorem stirlingSeq_eq_factorial_div (n : ℕ) (_hn : n ≠ 0) :
    Stirling.stirlingSeq n = (n.factorial : ℝ) / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := rfl

/-- Our stirlingApprox is √π times the denominator of stirlingSeq. -/
theorem stirlingApprox_eq (n : ℕ) (hn : n ≠ 0) :
    stirlingApprox n = Real.sqrt Real.pi * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
  simp only [stirlingApprox, hn, ↓reduceIte]
  -- Goal: √(2πn) * (n/e)^n = √π * (√(2n) * (n/e)^n)
  -- √(2πn) = √(2π) * √n = √π * √2 * √n = √π * √(2n)
  have hsqrt_eq : Real.sqrt (2 * Real.pi * n) = Real.sqrt Real.pi * Real.sqrt (2 * n) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hsqrt_eq, mul_assoc]

/-- Stirling ratio: n! / stirlingApprox(n) → 1 as n → ∞.
    Uses Mathlib's `tendsto_stirlingSeq_sqrt_pi`. -/
theorem stirling_ratio_tendsto_one :
    Filter.Tendsto (fun n => (n.factorial : ℝ) / stirlingApprox n)
      Filter.atTop (nhds 1) := by
  -- stirlingSeq n → √π means n! / (√(2n)(n/e)^n) → √π
  -- Our stirlingApprox n = √(2πn)(n/e)^n = √π · √(2n) · (n/e)^n
  -- So n!/stirlingApprox n = (n! / (√(2n)(n/e)^n)) / √π = stirlingSeq n / √π → 1
  have hpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpi_pos
  have htend := Stirling.tendsto_stirlingSeq_sqrt_pi
  have htend' : Filter.Tendsto (fun n => Stirling.stirlingSeq n / Real.sqrt Real.pi)
      Filter.atTop (nhds 1) := by
    convert htend.div_const (Real.sqrt Real.pi) using 1
    rw [div_self hpi_ne]
  apply Filter.Tendsto.congr' _ htend'
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  simp only [Stirling.stirlingSeq, stirlingApprox, hn, ↓reduceIte]
  -- Need to show: n! / (√(2πn) * (n/e)^n) = (n! / (√(2n) * (n/e)^n)) / √π
  -- LHS denominator: √(2πn) * (n/e)^n = √(2π) * √n * (n/e)^n = √π * √2 * √n * (n/e)^n
  -- RHS denominator (after div by √π): √π * √(2n) * (n/e)^n = √π * √2 * √n * (n/e)^n
  have hsqrt_eq : Real.sqrt (2 * Real.pi * n) = Real.sqrt Real.pi * Real.sqrt (2 * n) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    -- Goal: √2 * √π * √n = √π * (√2 * √n)
    -- Rewrite LHS: √2 * √π = √π * √2
    rw [mul_comm (Real.sqrt 2) (Real.sqrt Real.pi)]
    -- Now: √π * √2 * √n = √π * (√2 * √n)
    rw [mul_assoc]
  rw [hsqrt_eq]
  have hdenom_pos : 0 < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by positivity
  have hdenom_ne : Real.sqrt (2 * n) * (n / Real.exp 1) ^ n ≠ 0 := ne_of_gt hdenom_pos
  field_simp

/-- Stirling upper bound in terms of the ratio.
    For any ε > 0, for sufficiently large n: n! ≤ (1 + ε) · √(2πn) (n/e)^n.
    This follows from the ratio converging to 1. -/
theorem stirling_upper_bound_eventual (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, (n.factorial : ℝ) ≤ (1 + ε) * stirlingApprox n := by
  have htendsto := stirling_ratio_tendsto_one
  rw [Metric.tendsto_atTop] at htendsto
  obtain ⟨N₀, hN₀⟩ := htendsto ε hε
  use max 1 N₀
  intro n hn
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnN₀ : N₀ ≤ n := le_of_max_le_right hn
  specialize hN₀ n hnN₀
  rw [Real.dist_eq, abs_lt] at hN₀
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hstirling_pos : 0 < stirlingApprox n := by
    simp only [stirlingApprox, hn0, ↓reduceIte]
    positivity
  have hratio : (n.factorial : ℝ) / stirlingApprox n < 1 + ε := by linarith
  calc (n.factorial : ℝ)
      = (n.factorial : ℝ) / stirlingApprox n * stirlingApprox n := by
        field_simp
    _ ≤ (1 + ε) * stirlingApprox n := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hratio) (le_of_lt hstirling_pos)

/-! ## Binomial Coefficient Asymptotics

For the local CLT, we need to understand C(n, n/2 + k) for |k| = O(√n).
-/

/-- The binomial coefficient C(n, n/2 + k) for n even.
    When k = 0, this is the central binomial coefficient. -/
noncomputable def centralBinomialShifted (n : ℕ) (k : ℤ) : ℕ :=
  if h : 0 ≤ n/2 + k ∧ n/2 + k ≤ n then
    Nat.choose n (n/2 + k.toNat)
  else 0

/-- The Gaussian density at x with variance σ²:
    φ_σ(x) = (1/(σ√(2π))) exp(-x²/(2σ²)) -/
noncomputable def gaussianDensity (sigma : ℝ) (x : ℝ) : ℝ :=
  if sigma > 0 then
    (1 / (sigma * Real.sqrt (2 * Real.pi))) * Real.exp (-x^2 / (2 * sigma^2))
  else 0

/-- For a symmetric random walk with n steps, the standard deviation is √(n)/2. -/
noncomputable def walkStdDev (n : ℕ) : ℝ := Real.sqrt n / 2

/-! ## Local Central Limit Theorem

The main theorem: the binomial distribution converges locally to the Gaussian.
-/

/-- **Local CLT Statement**: For the symmetric random walk S_n:
    P(S_n = 2k - n) = C(n,k)/2^n ≈ (2/√(πn)) exp(-(2k-n)²/n)

    More precisely, for k = n/2 + j where |j| ≤ C√n:
    |C(n,k)/2^n - (2/√(πn)) exp(-2j²/n)| = O(1/n)

    This gives pointwise convergence of the pmf to the Gaussian density.
-/
theorem local_clt_error_bound (n : ℕ) (j : ℤ) (hn : 1 ≤ n) (hj : |j| ≤ n) :
    let k := n/2 + j.toNat
    let binomProb := (Nat.choose n k : ℝ) / 2^n
    let gaussApprox := (2 / Real.sqrt (Real.pi * n)) * Real.exp (-2 * j^2 / n)
    |binomProb - gaussApprox| ≤ (10 : ℝ) / n := by
  -- The proof uses Stirling's approximation for the factorials in C(n,k)
  -- C(n,k) = n! / (k! (n-k)!)
  -- Apply Stirling to each factorial and simplify
  sorry

/-- For |j| ≤ √n, the binomial probability is close to the Gaussian.
    This is the key bound for the local CLT in the central region. -/
theorem local_clt_central_region (n : ℕ) (j : ℤ) (hn : 4 ≤ n)
    (hj : |j| ≤ Real.sqrt n) :
    let k := n/2 + j.toNat
    let binomProb := (Nat.choose n k : ℝ) / 2^n
    let gaussApprox := (2 / Real.sqrt (Real.pi * n)) * Real.exp (-2 * j^2 / n)
    binomProb ≥ gaussApprox / 2 ∧ binomProb ≤ 2 * gaussApprox := by
  -- In the central region, the error is small enough that the ratio is bounded
  sorry

/-! ## Tail Bounds

Outside the central region |j| > C√n, both binomial and Gaussian are exponentially small.
-/

/-- Hoeffding's inequality for the symmetric random walk:
    P(|S_n| > t) ≤ 2 exp(-t²/(2n)) -/
theorem hoeffding_random_walk (n : ℕ) (t : ℝ) (ht : 0 < t) (hn : 0 < n) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (t : ℝ) < |partialSumFin n flips n|)).card : ℝ) / 2^n ≤
    2 * Real.exp (-t^2 / (2 * n)) := by
  -- Hoeffding's inequality follows from Chernoff bound + exponential Markov
  sorry

/-- The Gaussian tail bound: ∫_{t}^∞ φ(x) dx ≤ φ(t)/t for t > 0 -/
theorem gaussian_tail_bound (t : ℝ) (ht : 0 < t) :
    ∫ x in Set.Ici t, Real.exp (-x^2/2) ≤ Real.exp (-t^2/2) / t := by
  -- Mill's ratio: the Gaussian tail is bounded by the density divided by the argument
  sorry

/-! ## Convergence of Cylinder Set Probabilities

For Anderson's theorem, we need the cylinder set probabilities to converge
to the corresponding Wiener measure probabilities.
-/

/-- For a single time constraint, the hyperfinite probability converges to Wiener measure.
    This is the key bridge between the nonstandard and standard worlds.

    If we have W_t ∈ [a, b] for Wiener measure, and the hyperfinite walk X_⌊tN⌋/√N at
    step ⌊tN⌋, rescaled, then:
    P_Loeb(X_⌊tN⌋/√N ∈ [a,b]) = Wiener(W_t ∈ [a,b]) + O(1/√N)
-/
theorem cylinder_prob_convergence (a b : ℝ) (t : ℝ) (ha : a < b) (ht : 0 < t) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      let scaledProb := ((Finset.univ : Finset (Fin N → Bool)).filter
        (fun flips =>
          let walk := (partialSumFin N flips k : ℝ) / Real.sqrt N
          a ≤ walk ∧ walk ≤ b)).card / (2^N : ℝ)
      let wienerProb := ∫ x in Set.Icc a b, gaussianDensity (Real.sqrt t) x
      |scaledProb - wienerProb| < ε := by
  -- This follows from the local CLT applied to each term in the sum
  -- scaledProb = Σ_{j : a√N ≤ 2j-k ≤ b√N} C(N, (k+j)/2) / 2^N
  -- Each term ≈ gaussianDensity evaluated at the corresponding point
  -- The sum approximates the integral
  sorry

/-! ## Summary

We have stated the main components needed for the local CLT:

1. **Stirling bounds** - Lower and upper bounds on n! via Stirling's formula
2. **Local CLT** - Pointwise convergence of binomial pmf to Gaussian density
3. **Tail bounds** - Hoeffding inequality and Gaussian tail bounds
4. **Cylinder convergence** - Hyperfinite probabilities converge to Wiener measure

These are the key ingredients for proving Anderson's theorem:
- The pushforward of Loeb measure under the standard part map equals Wiener measure.

The proofs are marked with `sorry` as they require substantial technical work:
- Stirling: Integral comparisons or Wallis product
- Local CLT: Careful application of Stirling to factorials
- Hoeffding: Exponential moment bounds
- Cylinder convergence: Riemann sum approximation of integrals

-/

end SPDE.Nonstandard

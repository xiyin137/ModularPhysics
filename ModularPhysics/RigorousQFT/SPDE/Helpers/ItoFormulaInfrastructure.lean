/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.BrownianMotion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Itô Formula Infrastructure

Infrastructure for proving the Itô formula martingale property.
This file provides the analytical estimates (Gaussian moments, BM quadratic variation
convergence) that feed into the partition-based Itô formula proof.
The martingale property itself follows from the L² limit infrastructure
in `ItoIntegralProperties.lean`.

## Main results

- `fourth_moment_gaussianReal`: ∫ x⁴ d(gaussianReal 0 v) = 3v²
- `IsGaussian.fourth_moment`: E[X⁴] = 3σ⁴ for X ~ N(0, σ²)
- `BrownianMotion.increment_fourth_moment`: E[(ΔW)⁴] = 3(Δt)²
- `BrownianMotion.increment_sq_minus_dt_variance`: E[((ΔW)²-Δt)²] = 2(Δt)²
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

/-! ## Derivative computations for exp(v·t²/2)

We compute the first four derivatives of `fun t ↦ rexp (v * t ^ 2 / 2)` step by step.
Each function in the chain has the form `p(t) * rexp(v * t² / 2)` where p is a polynomial.

- f₀(t) = 1 · exp(v·t²/2)
- f₁(t) = (v·t) · exp(v·t²/2)
- f₂(t) = (v + v²·t²) · exp(v·t²/2)
- f₃(t) = (3v²·t + v³·t³) · exp(v·t²/2)
- f₄(t) = (3v² + 6v³·t² + v⁴·t⁴) · exp(v·t²/2)

and f₄(0) = 3v².
-/

variable (v : ℝ)

/-- The Gaussian MGF-type function exp(v·t²/2) has derivative v·t·exp(v·t²/2). -/
private lemma hasDerivAt_gauss_exp (t : ℝ) :
    HasDerivAt (fun t => rexp (v * t ^ 2 / 2)) (v * t * rexp (v * t ^ 2 / 2)) t := by
  have hg : HasDerivAt (fun t => v * t ^ 2 / 2) (v * t) t := by
    have h := (hasDerivAt_pow 2 t).const_mul v |>.div_const 2
    convert h using 1; ring
  convert hg.exp using 1; ring

/-- General derivative lemma: if f(t) = p(t) · exp(v·t²/2) and HasDerivAt p p' t,
    then HasDerivAt f ((p' + v·t·p(t)) · exp(v·t²/2)) t. -/
private lemma hasDerivAt_poly_mul_gauss (p : ℝ → ℝ) (p'_val : ℝ) (t : ℝ)
    (hp : HasDerivAt p p'_val t) :
    HasDerivAt (fun t => p t * rexp (v * t ^ 2 / 2))
      ((p'_val + v * t * p t) * rexp (v * t ^ 2 / 2)) t := by
  have hexp := hasDerivAt_gauss_exp v t
  convert hp.mul hexp using 1; ring

/-- Step 0→1: deriv exp(v·t²/2) = v·t · exp(v·t²/2) -/
private lemma deriv_f0 :
    deriv (fun t => rexp (v * t ^ 2 / 2)) =
      fun t => v * t * rexp (v * t ^ 2 / 2) := by
  ext t; exact (hasDerivAt_gauss_exp v t).deriv

/-- Step 1→2: deriv (v·t · exp(v·t²/2)) t = (v + v²·t²) · exp(v·t²/2) -/
private lemma deriv_f1 (t : ℝ) :
    deriv (fun t => v * t * rexp (v * t ^ 2 / 2)) t =
      (v + v ^ 2 * t ^ 2) * rexp (v * t ^ 2 / 2) := by
  have hp : HasDerivAt (fun t => v * t) v t := by
    simpa [Function.id_def, mul_one] using (hasDerivAt_id t).const_mul v
  have := (hasDerivAt_poly_mul_gauss v (fun t => v * t) v t hp).deriv
  convert this using 1; ring

/-- Step 2→3: deriv ((v + v²·t²) · exp(v·t²/2)) t = (3v²·t + v³·t³) · exp(v·t²/2) -/
private lemma deriv_f2 (t : ℝ) :
    deriv (fun t => (v + v ^ 2 * t ^ 2) * rexp (v * t ^ 2 / 2)) t =
      (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * rexp (v * t ^ 2 / 2) := by
  have hp : HasDerivAt (fun t => v + v ^ 2 * t ^ 2) (2 * v ^ 2 * t) t := by
    have h1 := (hasDerivAt_pow 2 t).const_mul (v ^ 2)
    have h2 := (hasDerivAt_const t v).add h1
    convert h2 using 1; ring
  have := (hasDerivAt_poly_mul_gauss v (fun t => v + v ^ 2 * t ^ 2) (2 * v ^ 2 * t) t hp).deriv
  convert this using 1; ring

/-- Step 3→4: deriv ((3v²·t + v³·t³) · exp(v·t²/2)) t =
    (3v² + 6v³·t² + v⁴·t⁴) · exp(v·t²/2) -/
private lemma deriv_f3 (t : ℝ) :
    deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * rexp (v * t ^ 2 / 2)) t =
      (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * rexp (v * t ^ 2 / 2) := by
  have hp : HasDerivAt (fun t => 3 * v ^ 2 * t + v ^ 3 * t ^ 3)
      (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t := by
    have h1 := (hasDerivAt_id t).const_mul (3 * v ^ 2)
    have h2 := (hasDerivAt_pow 3 t).const_mul (v ^ 3)
    convert h1.add h2 using 1; ring
  have := (hasDerivAt_poly_mul_gauss v (fun t => 3 * v ^ 2 * t + v ^ 3 * t ^ 3)
    (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t hp).deriv
  convert this using 1; ring

/-- The fourth derivative of exp(v·t²/2) at 0 is 3v².
    This combines the four derivative steps and evaluates at 0. -/
private lemma fourth_deriv_gauss_at_zero :
    deriv (fun t => deriv (fun t => deriv (fun t => deriv
      (fun t => rexp (v * t ^ 2 / 2)) t) t) t) 0 = 3 * v ^ 2 := by
  -- Replace each deriv layer with the explicit formula
  conv_lhs =>
    arg 1; ext t; arg 1; ext t; arg 1; ext t
    rw [(hasDerivAt_gauss_exp v t).deriv]
  conv_lhs =>
    arg 1; ext t; arg 1; ext t
    rw [deriv_f1 v t]
  conv_lhs =>
    arg 1; ext t
    rw [deriv_f2 v t]
  rw [deriv_f3 v 0]
  simp [exp_zero]

/-! ## Gaussian Fourth Moment -/

/-- The fourth central moment of a Gaussian distribution: E[(X-μ)⁴] = 3v².

Proof: Use the MGF approach (following the Mathlib `variance_fun_id_gaussianReal` pattern).
- Shift to zero mean via `gaussianReal_map_sub_const`
- MGF of N(0, v) is M(t) = exp(v·t²/2)  (from `mgf_fun_id_gaussianReal`)
- E[X⁴] = iteratedDeriv 4 M 0  (from `iteratedDeriv_mgf_zero`)
- Evaluate via `fourth_deriv_gauss_at_zero`
-/
theorem fourth_moment_gaussianReal (μ_val : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ_val) ^ 4 ∂gaussianReal μ_val v = 3 * (↑v : ℝ) ^ 2 := by
  calc ∫ x, (x - μ_val) ^ 4 ∂gaussianReal μ_val v
  _ = ∫ x, x ^ 4 ∂(gaussianReal μ_val v).map (fun x => x - μ_val) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ x, x ^ 4 ∂gaussianReal 0 v := by
    simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 4 (mgf (fun x => x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = 3 * ↑v ^ 2 := by
    rw [mgf_fun_id_gaussianReal]
    simp only [zero_mul, zero_add]
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    exact fourth_deriv_gauss_at_zero ↑v

/-! ## IsGaussian Fourth Moment -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The fourth moment of a zero-mean Gaussian random variable: E[X⁴] = 3σ⁴.
    Uses the pushforward to `gaussianReal` and the fourth moment computation. -/
theorem Probability.IsGaussian.fourth_moment {X : Ω → ℝ} {μ : Measure Ω} {variance : ℝ}
    (h : IsGaussian X μ 0 variance) :
    ∫ ω, (X ω) ^ 4 ∂μ = 3 * variance ^ 2 := by
  have hX_am : AEMeasurable X μ := h.integrable.aemeasurable
  have hmap := h.map_eq_gaussianReal
  -- Transfer: ∫ (X ω)⁴ dμ = ∫ x⁴ d(μ.map X)
  have htransfer : ∫ ω, (X ω) ^ 4 ∂μ = ∫ x, x ^ 4 ∂(μ.map X) :=
    (integral_map hX_am (by fun_prop : AEStronglyMeasurable (fun x => x ^ 4) (μ.map X))).symm
  rw [htransfer, hmap]
  -- ∫ x⁴ d(gaussianReal 0 ⟨variance, _⟩) = 3 * variance²
  have h0 := fourth_moment_gaussianReal 0 ⟨variance, h.variance_nonneg⟩
  simpa [sub_zero] using h0

/-! ## BM Increment Fourth Moment -/

variable {μ : Measure Ω}

/-- Fourth moment of BM increments: E[(W_t - W_s)⁴] = 3(t-s)².
    Follows directly from the Gaussian fourth moment since W_t - W_s ~ N(0, t-s). -/
theorem BrownianMotion.increment_fourth_moment (W : BrownianMotion Ω μ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 4 ∂μ =
      3 * (t - s) ^ 2 :=
  (W.gaussian_increments s t hs hst).fourth_moment

/-- Variance of (ΔW)² - Δt: E[((W_t - W_s)² - (t-s))²] = 2(t-s)².
    This is the key estimate for BM quadratic variation L² convergence.

    Proof: Expand (X² - c)² = X⁴ - 2c·X² + c² and use E[X⁴] = 3c², E[X²] = c
    where c = t-s and X = W_t - W_s ~ N(0, c). -/
theorem BrownianMotion.increment_sq_minus_dt_variance (W : BrownianMotion Ω μ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, ((W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 - (t - s)) ^ 2 ∂μ =
      2 * (t - s) ^ 2 := by
  -- Derive probability measure from Gaussian increments
  haveI : IsProbabilityMeasure μ := (W.gaussian_increments s t hs hst).isProbabilityMeasure
  -- Known moments
  have hX4 := W.increment_fourth_moment s t hs hst
  have hX2 := W.increment_variance s t hs hst
  have hX4_int := W.increment_all_moments s t hs hst 4
  have hX2_int := W.increment_sq_integrable s t hs hst
  -- Rewrite (X² - c)² = X⁴ + (-2c)·X² + c²  (using + throughout for integral_add)
  have hexp : ∀ ω, ((W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 -
      (t - s)) ^ 2 =
    (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 4 +
    ((-2 * (t - s)) * (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 +
    (t - s) ^ 2) := fun ω => by ring
  simp_rw [hexp]
  -- Explicitly typed integrability proofs so integral_add can match pointwise
  have hint_bc : Integrable (fun ω =>
      (-2 * (t - s)) * (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 +
      (t - s) ^ 2) μ :=
    (hX2_int.const_mul _).add (integrable_const _)
  have hint_b : Integrable (fun ω =>
      (-2 * (t - s)) * (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2) μ :=
    hX2_int.const_mul _
  -- Split ∫(A + (B + C)) = ∫ A + (∫ B + ∫ C)
  rw [integral_add hX4_int hint_bc]
  rw [integral_add hint_b (integrable_const _)]
  rw [integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  rw [hX4, hX2]; ring

/-! ## BM Quadratic Variation L² Convergence -/

/-- Sum of squared BM increments along a uniform partition of [0, T] with n subintervals.
    QV_n(ω) = Σᵢ₌₀ⁿ⁻¹ (W((i+1)T/n) - W(iT/n))² -/
def bmQVSum (W : BrownianMotion Ω μ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    (W.toAdapted.process ((↑i + 1) * T / ↑n) ω -
     W.toAdapted.process (↑i * T / ↑n) ω) ^ 2

/-- The L² distance of the QV sum from T is bounded by 2T²/n for uniform partitions.
    E[|QV_n - T|²] ≤ 2T²/n.

    Proof strategy: By independence of BM increments on disjoint intervals,
    the variance of the sum equals the sum of variances.
    Each Yᵢ = (ΔWᵢ)² - T/n has E[Yᵢ] = 0 and E[Yᵢ²] = 2(T/n)² by
    `increment_sq_minus_dt_variance`. By independence, E[(ΣYᵢ)²] = ΣE[Yᵢ²] = n·2(T/n)² = 2T²/n. -/
theorem bm_qv_sum_L2_bound (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (hn : 0 < n) :
    ∫ ω, (bmQVSum W T n ω - T) ^ 2 ∂μ ≤ 2 * T ^ 2 / ↑n := by
  sorry

/-- The QV sum converges to T in L² as n → ∞.
    E[|QV_n - T|²] → 0. -/
theorem bm_qv_L2_convergence (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n => ∫ ω, (bmQVSum W T (n + 1) ω - T) ^ 2 ∂μ)
      atTop (nhds 0) := by
  -- Squeeze between 0 and 2T²/(n+1) → 0
  apply squeeze_zero
  · intro n; positivity
  · intro n; exact bm_qv_sum_L2_bound W T hT (n + 1) (Nat.succ_pos n)
  · -- 2T²/(n+1) → 0
    have h : (fun n : ℕ => 2 * T ^ 2 / (↑(n + 1) : ℝ)) =
        (fun n : ℕ => (2 * T ^ 2) * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = (2 * T ^ 2) * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

end SPDE
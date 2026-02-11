/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Helpers.CommonRefinement
import ModularPhysics.RigorousQFT.SPDE.Helpers.SimpleProcessLinear
import ModularPhysics.RigorousQFT.SPDE.Probability.IndependenceHelpers

/-!
# Simple Process Isometry at Time t

This file proves the time-parameterized Itô isometry for simple processes:

  E[(∫₀ᵗ H dW)²] = E[∫₀ᵗ H(s)² ds]

where the LHS uses `stochasticIntegral_at` and the RHS uses `valueAtTime`.

## Main Results

* `SimpleProcess.isometry_at` — The quadratic isometry at time t
* `SimpleProcess.bilinear_isometry_at` — The bilinear isometry at time t

## Strategy

The proof uses the min-capped reformulation `stochasticIntegral_at_eq_min`:
  S(t) = Σᵢ Hᵢ · (W(min(tᵢ₊₁,t)) - W(min(tᵢ,t)))

Then:
1. Pythagoras: E[(Σaᵢ)²] = Σ E[aᵢ²] (cross terms vanish)
2. Diagonal: E[aᵢ²] = E[Hᵢ²] · (min(tᵢ₊₁,t) - min(tᵢ,t))
3. Connection: Σ E[Hᵢ²] · Δtᵢ_capped = E[∫₀ᵗ val² ds]

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ## Cross-term vanishing for min-capped increments -/

/-- Cross-term vanishing for min-capped increments: for i < j,
    E[Hᵢ·ΔWᵢ_cap · Hⱼ·ΔWⱼ_cap] = 0.

    The min-capped increment at j is either 0 (if tⱼ ≥ t) or
    starts at tⱼ > tᵢ₊₁, giving independence with the i-factor. -/
theorem cross_term_zero_at (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (_ht : 0 ≤ t)
    (i j : Fin H.n)
    (hi : (i : ℕ) + 1 < H.n) (hj : (j : ℕ) + 1 < H.n)
    (hij : (i : ℕ) < (j : ℕ)) :
    ∫ ω, (H.values i ω *
           (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
            W.process (min (H.times i) t) ω)) *
          (H.values j ω *
           (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
            W.process (min (H.times j) t) ω)) ∂μ = 0 := by
  -- Successor comparison helpers
  have hj_succ : j < (⟨(j : ℕ) + 1, hj⟩ : Fin H.n) := by
    show (j : ℕ) < (j : ℕ) + 1; omega
  have hi_succ : i < (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) := by
    show (i : ℕ) < (i : ℕ) + 1; omega
  -- If the j-increment is trivial (both endpoints capped to t), it's 0
  by_cases hjt : H.times j ≥ t
  · -- min(t_j, t) = min(t_{j+1}, t) = t, so ΔW_j_cap = 0
    have h1 : min (H.times j) t = t := min_eq_right hjt
    have h2 : min (H.times ⟨j + 1, hj⟩) t = t :=
      min_eq_right (le_trans hjt (le_of_lt (H.increasing j ⟨j + 1, hj⟩ hj_succ)))
    simp only [h1, h2, sub_self, mul_zero, MeasureTheory.integral_zero]
  · push_neg at hjt
    -- min(t_j, t) = t_j since t_j < t
    have hj_min : min (H.times j) t = H.times j := min_eq_left (le_of_lt hjt)
    -- Regroup: (Hᵢ·ΔWᵢ_cap) · (Hⱼ·ΔWⱼ_cap) = (Hᵢ·ΔWᵢ_cap·Hⱼ) · ΔWⱼ_cap
    have hregroup : ∀ ω,
        (H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω)) *
        (H.values j ω *
          (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
           W.process (min (H.times j) t) ω)) =
        (H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) *
        (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
         W.process (min (H.times j) t) ω) := by
      intro ω; ring
    simp_rw [hregroup, hj_min]
    -- Ordering helpers
    have htj_nn := hH_times_nn j
    have hjj1 : H.times j < min (H.times ⟨j + 1, hj⟩) t :=
      lt_min (H.increasing j ⟨j + 1, hj⟩ hj_succ) hjt
    have hij_fin : i < j := Fin.lt_def.mpr hij
    have hi_le_j : H.times i ≤ H.times j :=
      le_of_lt (H.increasing i j hij_fin)
    have hi1_le_j : H.times ⟨i + 1, hi⟩ ≤ H.times j := by
      by_cases h : (i : ℕ) + 1 = (j : ℕ)
      · have : (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) = j := by ext; exact h
        rw [this]
      · exact le_of_lt (H.increasing ⟨(i : ℕ) + 1, hi⟩ j (by show (i : ℕ) + 1 < (j : ℕ); omega))
    -- The product factor (Hᵢ·ΔWᵢ_cap·Hⱼ) is F_{t_j}-measurable
    have hX_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times j)) _
        (fun ω => H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) := by
      exact ((hH_adapted i).mono (W.F.mono _ _ hi_le_j) le_rfl |>.mul
        (((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_of_left_le hi1_le_j)) le_rfl).sub
         ((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_of_left_le hi_le_j)) le_rfl))).mul
        ((hH_adapted j).mono le_rfl le_rfl)
    -- The product factor is integrable (bounded × integrable pattern)
    have hX_int : Integrable
        (fun ω => H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) μ := by
      -- Regroup as (Hi * Hj) * ΔWi_cap
      have hregroup' : (fun ω => H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) =
          (fun ω => (H.values i ω * H.values j ω) *
            (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
             W.process (min (H.times i) t) ω)) := by
        ext ω; ring
      rw [hregroup']
      -- ΔWi_cap is integrable (L² hence L¹)
      have hΔWi_int := W.increment_integrable _ _
        (le_min (hH_times_nn i) _ht)
        (min_le_min_right t (le_of_lt (H.increasing i ⟨i + 1, hi⟩ hi_succ)))
      -- Hi * Hj is bounded
      obtain ⟨Ci, hCi⟩ := hH_bdd i
      obtain ⟨Cj, hCj⟩ := hH_bdd j
      apply Integrable.bdd_mul hΔWi_int
      · exact (((hH_adapted i).mono (W.F.le_ambient _) le_rfl).mul
          ((hH_adapted j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
    -- ΔW_j_cap is integrable
    have hY_int : Integrable
        (fun ω => W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
         W.process (H.times j) ω) μ :=
      W.increment_integrable _ _ htj_nn (le_of_lt hjj1)
    -- ΔW_j_cap has mean 0
    have hY_mean : ∫ ω, (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
        W.process (H.times j) ω) ∂μ = 0 :=
      W.increment_mean_zero _ _ htj_nn (le_of_lt hjj1)
    -- Independence: ΔW_j_cap is independent of F_{t_j}
    have hindep : Indep (W.F.σ_algebra (H.times j))
      (MeasurableSpace.comap (fun ω => W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
        W.process (H.times j) ω) inferInstance) μ :=
      W.independent_increments _ _ htj_nn (le_of_lt hjj1)
    -- Apply the key lemma: E[X·Y] = 0
    exact SPDE.Probability.integral_mul_zero_of_indep_zero_mean
      (W.F.le_ambient _) hX_meas hX_int hY_int hindep hY_mean

/-! ## The isometry at time t -/

/-- The isometry for simple processes at time t:
    E[(∫₀ᵗ H dW)²] = E[∫₀ᵗ H(s)² ds].

    Uses the min-capped reformulation of `stochasticIntegral_at`,
    Pythagoras (cross terms vanish), and diagonal computation. -/
theorem isometry_at (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, (H.stochasticIntegral_at W t ω) ^ 2 ∂μ =
    ∫ ω, (∫ s in Set.Icc 0 t, (H.valueAtTime s ω) ^ 2 ∂volume) ∂μ := by
  sorry

/-- Bilinear isometry at time t: E[S₁(t)·S₂(t)] = E[∫₀ᵗ val₁·val₂ ds].

    Proved by polarization from `isometry_at` combined with
    `exists_linear_simple_integral` for the common refinement. -/
theorem bilinear_isometry_at (H₁ H₂ : SimpleProcess F)
    (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH₁_adapted : ∀ i : Fin H₁.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H₁.times i)) _ (H₁.values i))
    (hH₂_adapted : ∀ i : Fin H₂.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H₂.times i)) _ (H₂.values i))
    (hH₁_bdd : ∀ i : Fin H₁.n, ∃ C : ℝ, ∀ ω, |H₁.values i ω| ≤ C)
    (hH₂_bdd : ∀ i : Fin H₂.n, ∃ C : ℝ, ∀ ω, |H₂.values i ω| ≤ C)
    (hH₁_nn : ∀ i : Fin H₁.n, 0 ≤ H₁.times i)
    (hH₂_nn : ∀ i : Fin H₂.n, 0 ≤ H₂.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, H₁.stochasticIntegral_at W t ω * H₂.stochasticIntegral_at W t ω ∂μ =
    ∫ ω, (∫ s in Set.Icc 0 t,
      H₁.valueAtTime s ω * H₂.valueAtTime s ω ∂volume) ∂μ := by
  sorry

end SimpleProcess

end SPDE

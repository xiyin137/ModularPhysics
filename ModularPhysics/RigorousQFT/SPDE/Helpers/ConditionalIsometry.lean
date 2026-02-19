/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Helpers.IsometryTheorems

/-!
# Conditional Itô Isometry

This file proves the conditional (set-integral) version of the Itô isometry:
for A ∈ F_s with s ≤ s₂ ≤ t₂,

  ∫_A [(SI(t₂)-SI(s₂))² - ∫_{s₂}^{t₂} σ² du] dμ = 0

This is the key ingredient for proving orthogonality of compensated squared
stochastic integral increments on disjoint intervals.

## Strategy

The proof uses L² limits from simple process approximations:

1. For each simple approximation Hₙ, define M_n(t) = SI_n(t)² - ∫₀ᵗ Hₙ²
2. Show ∫_A [M_n(t₂) - M_n(s₂)] = 0 (simple process compensated square martingale)
3. Show M_n → M in L¹
4. Conclude ∫_A [M(t₂) - M(s₂)] = 0

Step 2 uses the cross-term vanishing from the simple process martingale property
(existing `stochasticIntegral_at_martingale`) combined with the BM compensated
square set-integral factorization (from `quadratic_variation_compensator`).

## Main Results

* `ItoProcess.compensated_sq_setIntegral_zero` — The conditional isometry
* `ItoProcess.stoch_integral_squared_orthogonal` — Orthogonality (replaces sorry)

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3, Theorem 3.2.1
-/

noncomputable section

open MeasureTheory Set Filter

variable {Ω : Type*} [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

namespace SPDE

/-! ## Set-integral cross-term vanishing for stochastic integrals -/

/-- On a set A ∈ F_s, the cross-term SI(s)·(SI(t)-SI(s)) integrates to zero.
    This is the set-integral analogue of the cross-term in `stoch_integral_cross_term`. -/
theorem ItoProcess.setIntegral_cross_term_zero {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s) A) :
    ∫ ω in A, X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω) ∂μ = 0 := by
  -- Rewrite as full integral with indicator: ∫_A f·g = ∫ (1_A·f)·g
  rw [← integral_indicator (F.le_ambient s A hA)]
  simp_rw [indicator_mul_left]
  -- Apply orthogonality lemma with X = 1_A·SI(s), Y = SI(t)-SI(s)
  apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s)
  · -- 1_A·SI(s) is F_s-measurable
    exact (X.stoch_integral_adapted s).indicator hA
  · -- SI(t)-SI(s) is integrable
    exact (X.stoch_integral_integrable t (le_trans hs hst)).sub
      (X.stoch_integral_integrable s hs)
  · -- Product integrability: (1_A·SI(s))·(SI(t)-SI(s)) is integrable
    -- Use AM-GM: |ab| ≤ a²+b²
    have hSI_s_sq := X.stoch_integral_sq_integrable s hs
    have hSI_t_sq := X.stoch_integral_sq_integrable t (le_trans hs hst)
    apply Integrable.mono' ((hSI_s_sq.add hSI_t_sq).add hSI_s_sq)
    · exact ((X.stoch_integral_integrable s hs).indicator
        (F.le_ambient s A hA)).aestronglyMeasurable.mul
        ((X.stoch_integral_integrable t (le_trans hs hst)).sub
          (X.stoch_integral_integrable s hs)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, indicator_mul_left]
      by_cases hω : ω ∈ A
      · simp only [indicator_of_mem hω]
        rw [abs_mul]
        set a := |X.stoch_integral s ω|
        set b := |X.stoch_integral t ω - X.stoch_integral s ω|
        nlinarith [sq_nonneg (a - b), sq_abs (X.stoch_integral s ω),
          sq_abs (X.stoch_integral t ω - X.stoch_integral s ω),
          sq_abs (X.stoch_integral t ω)]
      · simp only [indicator_of_notMem hω, zero_mul, abs_zero]
        positivity
  · -- ∫_B (SI(t)-SI(s)) = 0 for B ∈ F_s (martingale property)
    intro B hB
    rw [integral_sub (X.stoch_integral_integrable t (le_trans hs hst)).integrableOn
        (X.stoch_integral_integrable s hs).integrableOn]
    exact sub_eq_zero.mpr (X.stoch_integral_martingale s t hs hst B hB)

/-- Set-integral squared increment decomposition:
    ∫_A (SI(t)-SI(s))² = ∫_A SI(t)² - ∫_A SI(s)²

    Follows from the set-integral cross-term vanishing. -/
theorem ItoProcess.setIntegral_sq_increment_eq_diff {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s) A) :
    ∫ ω in A, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
    ∫ ω in A, (X.stoch_integral t ω) ^ 2 ∂μ -
    ∫ ω in A, (X.stoch_integral s ω) ^ 2 ∂μ := by
  have hSI_s_sq := X.stoch_integral_sq_integrable s hs
  have hSI_t_sq := X.stoch_integral_sq_integrable t (le_trans hs hst)
  have hcross := X.setIntegral_cross_term_zero s t hs hst A hA
  -- Cross term integrability
  have hcross_int : Integrable
      (fun ω => X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω)) μ := by
    apply Integrable.mono' ((hSI_t_sq.add hSI_s_sq).add hSI_s_sq)
    · exact (X.stoch_integral_integrable s hs).aestronglyMeasurable.mul
        ((X.stoch_integral_integrable t (le_trans hs hst)).sub
          (X.stoch_integral_integrable s hs)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_mul]; nlinarith [sq_abs (X.stoch_integral s ω),
        sq_abs (X.stoch_integral t ω - X.stoch_integral s ω),
        sq_abs (X.stoch_integral t ω),
        sq_nonneg (|X.stoch_integral s ω| - |X.stoch_integral t ω - X.stoch_integral s ω|)]
  -- Suffices: ∫_A SI(t)² = ∫_A SI(s)² + ∫_A (SI(t)-SI(s))²
  -- Proof: SI(t)² = SI(s)² + 2·SI(s)·(SI(t)-SI(s)) + (SI(t)-SI(s))²
  -- and ∫_A [2·SI(s)·(SI(t)-SI(s))] = 0 by cross-term vanishing
  suffices h : ∫ ω in A, (X.stoch_integral t ω) ^ 2 ∂μ =
      ∫ ω in A, (X.stoch_integral s ω) ^ 2 ∂μ +
      ∫ ω in A, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ by linarith
  -- Split: ∫_A SI(t)² = ∫_A [SI(s)² + 2·cross + incr²]
  --                    = ∫_A SI(s)² + 2·∫_A cross + ∫_A incr²
  have h_step1 : ∫ ω in A, (X.stoch_integral t ω) ^ 2 ∂μ =
      ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
        2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω)) +
        (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ∂μ := by
    congr 1; ext ω; ring
  have h_step2 : ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
      2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω)) +
      (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ∂μ =
      ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
        2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω))) ∂μ +
      ∫ ω in A, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ :=
    integral_add (hSI_s_sq.integrableOn.add (hcross_int.const_mul 2).integrableOn)
      (si_increment_sq_integrable' X s t hs hst).integrableOn
  have h_step3 : ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
      2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω))) ∂μ =
      ∫ ω in A, (X.stoch_integral s ω) ^ 2 ∂μ +
      ∫ ω in A, 2 * (X.stoch_integral s ω *
        (X.stoch_integral t ω - X.stoch_integral s ω)) ∂μ :=
    integral_add hSI_s_sq.integrableOn (hcross_int.const_mul 2).integrableOn
  have h_step4 : ∫ ω in A, 2 * (X.stoch_integral s ω *
      (X.stoch_integral t ω - X.stoch_integral s ω)) ∂μ = 0 := by
    rw [show (fun ω => 2 * (X.stoch_integral s ω *
        (X.stoch_integral t ω - X.stoch_integral s ω))) =
        (fun ω => (2 : ℝ) * (X.stoch_integral s ω *
          (X.stoch_integral t ω - X.stoch_integral s ω))) from rfl,
      integral_const_mul, hcross, mul_zero]
  linarith

/-! ## Compensated square L¹ convergence -/

/-- L¹ convergence of the compensated square:
    ∫ |SI_n(t)² - SI(t)²| → 0 from L² convergence SI_n → SI.
    Uses Cauchy-Schwarz: |a²-b²| = |a-b|·|a+b|. -/
private theorem sq_L1_tendsto_of_L2 {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (approx : ℕ → SimpleProcess F)
    (hadapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i))
    (hbdd : ∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C)
    (hnn : ∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i)
    (t : ℝ) (ht : 0 ≤ t)
    (hL2 : Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
                                     X.stoch_integral t ω)^2 ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω,
      ‖(SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)^2 -
       (X.stoch_integral t ω)^2‖ ∂μ)
      atTop (nhds 0) := by
  -- Abbreviations
  set a := fun n ω => SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω
  set b := fun ω => X.stoch_integral t ω
  set ε := fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂μ
  set C := ∫ ω, (b ω) ^ 2 ∂μ
  -- Integrability
  have hb_sq : Integrable (fun ω => (b ω) ^ 2) μ := X.stoch_integral_sq_integrable t ht
  have hb_int : Integrable b μ := X.stoch_integral_integrable t ht
  have ha_int : ∀ n, Integrable (a n) μ := fun n =>
    SimpleProcess.stochasticIntegral_at_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) t ht
  have hdiff_sq : ∀ n, Integrable (fun ω => (a n ω - b ω) ^ 2) μ := fun n =>
    SimpleProcess.stochasticIntegral_at_sub_sq_integrable _ X.BM
      (hadapted n) (hbdd n) (hnn n) b hb_int hb_sq t ht
  -- Pointwise bound: ‖a²-b²‖ ≤ (a-b)² + 2·|a-b|·|b|
  have h_pw : ∀ n ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ≤
      (a n ω - b ω) ^ 2 + 2 * (|a n ω - b ω| * |b ω|) := by
    intro n ω
    rw [Real.norm_eq_abs]
    have : (a n ω) ^ 2 - (b ω) ^ 2 = (a n ω - b ω) * (a n ω + b ω) := by ring
    rw [this, abs_mul]
    have h1 : |a n ω + b ω| ≤ |a n ω - b ω| + 2 * |b ω| := by
      calc |a n ω + b ω| = |(a n ω - b ω) + 2 * b ω| := by ring_nf
        _ ≤ |a n ω - b ω| + |2 * b ω| := abs_add_le _ _
        _ = |a n ω - b ω| + 2 * |b ω| := by rw [abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0)]
    calc |a n ω - b ω| * |a n ω + b ω|
        ≤ |a n ω - b ω| * (|a n ω - b ω| + 2 * |b ω|) := by gcongr
      _ = |a n ω - b ω| ^ 2 + 2 * (|a n ω - b ω| * |b ω|) := by
          rw [show |a n ω - b ω| ^ 2 = |a n ω - b ω| * |a n ω - b ω| from sq _]; ring
      _ = (a n ω - b ω) ^ 2 + 2 * (|a n ω - b ω| * |b ω|) := by rw [sq_abs]
  -- Upper bound: ∫ ‖a²-b²‖ ≤ ε(n) + 2·√(ε(n))·√C
  have h_upper : ∀ n, ∫ ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ∂μ ≤
      ε n + 2 * Real.sqrt (ε n) * Real.sqrt C := by
    intro n
    -- Integrability of |a-b|·|b| via AM-GM domination
    have h_abs_prod : Integrable (fun ω => |a n ω - b ω| * |b ω|) μ :=
      ((hdiff_sq n).add hb_sq).mono'
        (AEStronglyMeasurable.mul
          (((ha_int n).sub hb_int).aestronglyMeasurable.norm.congr
            (ae_of_all _ fun ω => Real.norm_eq_abs _))
          (hb_int.aestronglyMeasurable.norm.congr
            (ae_of_all _ fun ω => Real.norm_eq_abs _)))
        (ae_of_all _ fun ω => by
          simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_abs]
          nlinarith [sq_abs (a n ω - b ω), sq_abs (b ω),
            sq_nonneg (|a n ω - b ω| - |b ω|)])
    -- Step 1: ∫ ‖a²-b²‖ ≤ ∫ [(a-b)² + 2|a-b||b|] = ε(n) + 2·∫|a-b||b|
    have h_int_bound : ∫ ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ∂μ ≤
        ε n + 2 * ∫ ω, |a n ω - b ω| * |b ω| ∂μ := by
      calc ∫ ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ∂μ
          ≤ ∫ ω, ((a n ω - b ω) ^ 2 + 2 * (|a n ω - b ω| * |b ω|)) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _)
              ((hdiff_sq n).add (h_abs_prod.const_mul 2))
              (ae_of_all _ (h_pw n))
        _ = ε n + 2 * ∫ ω, |a n ω - b ω| * |b ω| ∂μ := by
            rw [integral_add (hdiff_sq n) (h_abs_prod.const_mul 2),
              integral_const_mul]
    -- Step 2: ∫|a-b||b| ≤ √(ε(n))·√C by Cauchy-Schwarz
    have h_cs : ∫ ω, |a n ω - b ω| * |b ω| ∂μ ≤
        Real.sqrt (ε n) * Real.sqrt C := by
      have h_nn : 0 ≤ ∫ ω, |a n ω - b ω| * |b ω| ∂μ :=
        integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      -- Reduce to (∫|f||g|)² ≤ ε·C by squaring both sides
      suffices hsq : (∫ ω, |a n ω - b ω| * |b ω| ∂μ) ^ 2 ≤ ε n * C by
        rw [← Real.sqrt_sq h_nn, ← Real.sqrt_mul (integral_nonneg fun ω => sq_nonneg _)]
        exact Real.sqrt_le_sqrt hsq
      -- Cauchy-Schwarz: (∫|f||g|)² ≤ (∫|f|²)(∫|g|²) = (∫(a-b)²)(∫b²) = ε·C
      have habs_sq : ∀ x : ℝ, |x| ^ 2 = x ^ 2 := fun x => sq_abs x
      calc (∫ ω, |a n ω - b ω| * |b ω| ∂μ) ^ 2
          ≤ (∫ ω, (|a n ω - b ω|) ^ 2 ∂μ) * (∫ ω, (|b ω|) ^ 2 ∂μ) :=
            integral_cauchy_schwarz_sq
              ((hdiff_sq n).congr (ae_of_all _ fun ω => (habs_sq _).symm))
              (hb_sq.congr (ae_of_all _ fun ω => (habs_sq _).symm))
              h_abs_prod
        _ = ε n * C := by
            congr 1 <;> exact integral_congr_ae (ae_of_all _ fun ω => habs_sq _)
    linarith
  -- Squeeze: 0 ≤ ∫‖a²-b²‖ ≤ ε(n) + 2√ε(n)√C → 0
  have h_upper_tends : Tendsto (fun n => ε n + 2 * Real.sqrt (ε n) * Real.sqrt C)
      atTop (nhds 0) := by
    have h_sqrt_ε : Tendsto (fun n => Real.sqrt (ε n)) atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hL2
      rwa [Function.comp_def, Real.sqrt_zero] at this
    have : (0 : ℝ) = 0 + 2 * 0 * Real.sqrt C := by ring
    rw [this]
    exact hL2.add ((h_sqrt_ε.const_mul 2).mul_const _)
  exact squeeze_zero
    (fun n => integral_nonneg fun ω => norm_nonneg _)
    h_upper
    h_upper_tends

/-- L¹ convergence of the diffusion integral:
    ∫ |∫₀ᵗ Hₙ² - ∫₀ᵗ σ²| → 0 from integrand L² convergence.

    Strategy: |∫ Hₙ² - ∫ σ²| ≤ ∫ |Hₙ²-σ²| ≤ ∫(Hₙ-σ)² + 2Mσ·∫|Hₙ-σ|
    ≤ δₙ(ω) + 2Mσ√t·√δₙ(ω) where δₙ = ∫(Hₙ-σ)².
    Then E[δₙ] → 0 and E[√δₙ] ≤ √E[δₙ] → 0 by Jensen. -/
private theorem diffusion_integral_L1_tendsto {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (approx : ℕ → SimpleProcess F)
    (hbdd : ∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t)
    (hL2_int : Tendsto
      (fun n => ∫ ω, (∫ s in Icc 0 t,
        (SimpleProcess.valueAtTime (approx n) s ω - X.diffusion s ω) ^ 2 ∂volume) ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω,
      ‖(∫ s in Icc 0 t, (SimpleProcess.valueAtTime (approx n) s ω)^2 ∂volume) -
       (∫ s in Icc 0 t, (X.diffusion s ω)^2 ∂volume)‖ ∂μ)
      atTop (nhds 0) := by
  -- Abbreviations
  set H := fun n s ω => SimpleProcess.valueAtTime (approx n) s ω
  set σ := fun s ω => X.diffusion s ω
  set δ := fun n ω => ∫ s in Icc 0 t, (H n s ω - σ s ω) ^ 2 ∂volume
  set ε := fun n => ∫ ω, δ n ω ∂μ
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hMσ_nn : 0 ≤ Mσ := le_trans (abs_nonneg _) (hMσ 0 (Classical.arbitrary Ω))
  -- Pointwise bound: |∫ Hₙ²-σ²| ≤ δₙ(ω) + 2Mσ√t·√δₙ(ω)
  -- Uses |H²-σ²| = |H-σ||H+σ| ≤ |H-σ|(|H-σ|+2Mσ) = (H-σ)² + 2Mσ|H-σ|
  -- Then ∫₀ᵗ |H-σ| ≤ √t · √δ by Cauchy-Schwarz on time integral
  have h_pw : ∀ n ω,
      ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
       (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ≤
      δ n ω + 2 * Mσ * Real.sqrt t * Real.sqrt (δ n ω) := by
    intro n ω
    -- Measurability
    have hσ_meas : Measurable (fun s => σ s ω) :=
      X.diffusion_jointly_measurable.comp (measurable_id.prodMk measurable_const)
    have hH_meas : Measurable (fun s => H n s ω) :=
      (SimpleProcess.valueAtTime_jointly_measurable (approx n)).comp
        (measurable_id.prodMk measurable_const)
    haveI h_fin : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    -- ω-dependent bound on |H|: step function → finitely many values
    obtain ⟨MH, hMH_nn, hMH⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |H n s ω| ≤ M := by
      refine ⟨(∑ j : Fin (approx n).n, |(approx n).values j ω|) + 1,
        add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) one_pos.le, fun s => ?_⟩
      show |SimpleProcess.valueAtTime (approx n) s ω| ≤ _
      unfold SimpleProcess.valueAtTime; split
      · next h =>
        exact le_trans (Finset.single_le_sum (fun j _ => abs_nonneg ((approx n).values j ω))
          (Finset.mem_univ h.choose)) (le_add_of_nonneg_right one_pos.le)
      · simp; exact add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) one_pos.le
    -- Integrability on Icc 0 t (bounded measurable on finite measure set)
    have hH_sq_int : IntegrableOn (fun s => (H n s ω)^2) (Icc 0 t) volume :=
      (integrable_const (MH^2)).mono'
        ((hH_meas.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (H n s ω)^2 = |H n s ω|^2 := (sq_abs _).symm
            _ ≤ MH^2 := pow_le_pow_left₀ (abs_nonneg _) (hMH s) 2)
    have hσ_sq_int : IntegrableOn (fun s => (σ s ω)^2) (Icc 0 t) volume :=
      X.diffusion_sq_time_integrable ω t ht
    have hd_sq_int : IntegrableOn (fun s => (H n s ω - σ s ω)^2) (Icc 0 t) volume :=
      (integrable_const ((MH + Mσ)^2)).mono'
        (((hH_meas.sub hσ_meas).pow_const 2).stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (H n s ω - σ s ω)^2 = |H n s ω - σ s ω|^2 := (sq_abs _).symm
            _ ≤ (MH + Mσ)^2 := by
                apply pow_le_pow_left₀ (abs_nonneg _)
                calc |H n s ω - σ s ω|
                    ≤ |H n s ω| + |σ s ω| := by
                      rw [show H n s ω - σ s ω = H n s ω + (-(σ s ω)) from sub_eq_add_neg _ _]
                      exact (abs_add_le _ _).trans (by rw [abs_neg])
                  _ ≤ MH + Mσ := add_le_add (hMH s) (hMσ s ω))
    -- |H-σ| integrable on Icc 0 t (from (H-σ)² integrable + finite measure, by Cauchy-Schwarz)
    have hd_abs_int : IntegrableOn (fun s => |H n s ω - σ s ω|) (Icc 0 t) volume :=
      (integrable_const (MH + Mσ)).mono'
        ((hH_meas.sub hσ_meas).stronglyMeasurable.aestronglyMeasurable.norm)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_abs]
          calc |H n s ω - σ s ω|
              ≤ |H n s ω| + |σ s ω| := by
                rw [show H n s ω - σ s ω = H n s ω + (-(σ s ω)) from sub_eq_add_neg _ _]
                exact (abs_add_le _ _).trans (by rw [abs_neg])
            _ ≤ MH + Mσ := add_le_add (hMH s) (hMσ s ω))
    -- Step 1: ‖∫H² - ∫σ²‖ = ‖∫(H²-σ²)‖ ≤ ∫‖H²-σ²‖
    have h_step1 : ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
        (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ≤
        ∫ s in Icc 0 t, ‖(H n s ω)^2 - (σ s ω)^2‖ ∂volume := by
      rw [← integral_sub hH_sq_int hσ_sq_int]
      exact norm_integral_le_integral_norm _
    -- Step 2: ∫‖H²-σ²‖ ≤ ∫(H-σ)² + 2Mσ∫|H-σ| = δ + 2Mσ∫|H-σ|
    have h_step2 : ∫ s in Icc 0 t, ‖(H n s ω)^2 - (σ s ω)^2‖ ∂volume ≤
        δ n ω + 2 * Mσ * ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume := by
      calc ∫ s in Icc 0 t, ‖(H n s ω)^2 - (σ s ω)^2‖ ∂volume
          ≤ ∫ s in Icc 0 t, ((H n s ω - σ s ω)^2 +
            2 * Mσ * |H n s ω - σ s ω|) ∂volume := by
              apply integral_mono_of_nonneg
                (ae_of_all _ fun s => norm_nonneg _)
                (hd_sq_int.add (hd_abs_int.const_mul (2 * Mσ)))
                (ae_of_all _ fun s => by
                  simp only [Pi.add_apply]
                  rw [Real.norm_eq_abs]
                  have h_factor : (H n s ω)^2 - (σ s ω)^2 =
                      (H n s ω - σ s ω) * (H n s ω + σ s ω) := by ring
                  rw [h_factor, abs_mul]
                  have h_bound_sum : |H n s ω + σ s ω| ≤
                      |H n s ω - σ s ω| + 2 * Mσ := by
                    calc |H n s ω + σ s ω|
                        = |(H n s ω - σ s ω) + 2 * σ s ω| := by ring_nf
                      _ ≤ |H n s ω - σ s ω| + |2 * σ s ω| := abs_add_le _ _
                      _ = |H n s ω - σ s ω| + 2 * |σ s ω| := by
                          rw [abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0)]
                      _ ≤ |H n s ω - σ s ω| + 2 * Mσ := by linarith [hMσ s ω]
                  calc |H n s ω - σ s ω| * |H n s ω + σ s ω|
                      ≤ |H n s ω - σ s ω| * (|H n s ω - σ s ω| + 2 * Mσ) :=
                        mul_le_mul_of_nonneg_left h_bound_sum (abs_nonneg _)
                    _ = |H n s ω - σ s ω| ^ 2 + 2 * Mσ * |H n s ω - σ s ω| := by ring
                    _ = (H n s ω - σ s ω) ^ 2 + 2 * Mσ * |H n s ω - σ s ω| := by
                        rw [sq_abs])
        _ = δ n ω + 2 * Mσ * ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume := by
            rw [integral_add hd_sq_int (hd_abs_int.const_mul _), integral_const_mul]
    -- Step 3: Cauchy-Schwarz on time integral: ∫|H-σ| ≤ √t · √δ
    have h_step3 : ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume ≤
        Real.sqrt t * Real.sqrt (δ n ω) := by
      have h_nn : 0 ≤ ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume :=
        integral_nonneg_of_ae (ae_of_all _ fun s => abs_nonneg _)
      suffices hsq : (∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume) ^ 2 ≤
          t * δ n ω by
        calc ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume
            = Real.sqrt ((∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume) ^ 2) :=
              (Real.sqrt_sq h_nn).symm
          _ ≤ Real.sqrt (t * δ n ω) := Real.sqrt_le_sqrt hsq
          _ = Real.sqrt t * Real.sqrt (δ n ω) := Real.sqrt_mul ht _
      -- CS: (∫|f|·1)² ≤ (∫|f|²)(∫1²) = (∫f²)(∫1) = δ·t
      have h_one_sq : ∫ s in Icc 0 t, (1:ℝ)^2 ∂volume = t := by
        simp [one_pow, integral_const]; linarith
      -- Apply CS with f = |H-σ|, g = 1
      have hcs := @integral_cauchy_schwarz_sq _ _ (volume.restrict (Icc (0:ℝ) t))
        (fun s => |H n s ω - σ s ω|) (fun _ => (1:ℝ))
        (hd_sq_int.congr (ae_of_all _ fun s => (sq_abs _).symm))
        (integrable_const _)
        (hd_abs_int.congr (ae_of_all _ fun s => (mul_one _).symm))
      -- hcs: (∫ |H-σ|·1)² ≤ (∫ |H-σ|²)(∫ 1²)
      -- Convert: |H-σ|·1 = |H-σ|, |H-σ|² = (H-σ)², 1² = t
      have hmul : ∫ s in Icc 0 t, |H n s ω - σ s ω| * (1:ℝ) ∂volume =
          ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume :=
        integral_congr_ae (ae_of_all _ fun s => mul_one _)
      have habs_sq : ∫ s in Icc 0 t, |H n s ω - σ s ω| ^ 2 ∂volume = δ n ω :=
        integral_congr_ae (ae_of_all _ fun s => sq_abs _)
      rw [hmul, habs_sq, h_one_sq] at hcs
      linarith
    have h_mul : 2 * Mσ * ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume ≤
        2 * Mσ * (Real.sqrt t * Real.sqrt (δ n ω)) :=
      mul_le_mul_of_nonneg_left h_step3 (by positivity)
    linarith
  -- Upper bound: E[‖...‖] ≤ ε(n) + 2Mσ√t·√ε(n)
  -- Uses Jensen: E[√δ] ≤ √(E[δ]) = √ε for probability measure
  have h_upper : ∀ n, ∫ ω,
      ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
       (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ∂μ ≤
      ε n + 2 * Mσ * Real.sqrt t * Real.sqrt (ε n) := by
    intro n
    -- Uniform bound on H_n
    obtain ⟨CH, hCH_nn, hCH⟩ :=
      SimpleProcess.valueAtTime_uniform_bounded (approx n) (hbdd n)
    -- δ non-negative and bounded
    have hδ_nn : ∀ ω, 0 ≤ δ n ω := fun ω => integral_nonneg fun s => sq_nonneg _
    haveI h_fin_icc : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have hδ_bound : ∀ ω, δ n ω ≤ (CH + Mσ) ^ 2 * t := by
      intro ω
      calc δ n ω
          ≤ ∫ s in Icc 0 t, (CH + Mσ) ^ 2 ∂volume := by
            apply integral_mono_of_nonneg (ae_of_all _ fun s => sq_nonneg _)
              (integrable_const _)
              (ae_of_all _ fun s => by
                calc (H n s ω - σ s ω) ^ 2 = |H n s ω - σ s ω| ^ 2 := (sq_abs _).symm
                  _ ≤ (CH + Mσ) ^ 2 := by
                      apply pow_le_pow_left₀ (abs_nonneg _)
                      exact (abs_sub _ _).trans (add_le_add (hCH s ω) (hMσ s ω)))
        _ = (CH + Mσ) ^ 2 * t := by
            rw [integral_const, smul_eq_mul, mul_comm]
            congr 1
            rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
              ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ t - 0), sub_zero]
    -- δ strongly measurable (via parametric integral of jointly measurable function)
    have hd_sq_sm : StronglyMeasurable
        (fun p : Ω × ℝ => (H n p.2 p.1 - σ p.2 p.1) ^ 2) :=
      (((SimpleProcess.valueAtTime_jointly_measurable (approx n)).comp
          measurable_swap).sub
        (X.diffusion_jointly_measurable.comp measurable_swap)).pow_const 2
      |>.stronglyMeasurable
    have hδ_sm : StronglyMeasurable (δ n) :=
      hd_sq_sm.integral_prod_right' (ν := volume.restrict (Icc (0:ℝ) t))
    -- δ integrable (bounded on probability space)
    have hδ_int : Integrable (δ n) μ :=
      (integrable_const ((CH + Mσ) ^ 2 * t)).mono' hδ_sm.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hδ_nn ω)]; exact hδ_bound ω)
    -- √δ measurable and integrable
    have hsqrtδ_sm : StronglyMeasurable (fun ω => Real.sqrt (δ n ω)) :=
      Real.continuous_sqrt.comp_stronglyMeasurable hδ_sm
    have hsqrtδ_int : Integrable (fun ω => Real.sqrt (δ n ω)) μ :=
      (integrable_const ((CH + Mσ) * Real.sqrt t)).mono' hsqrtδ_sm.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          calc Real.sqrt (δ n ω) ≤ Real.sqrt ((CH + Mσ) ^ 2 * t) :=
                Real.sqrt_le_sqrt (hδ_bound ω)
            _ = (CH + Mσ) * Real.sqrt t := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)])
    -- Step 1: ∫‖...‖ ≤ E[δ] + 2Mσ√t·E[√δ]
    have h_int_bound : ∫ ω, ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
        (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ∂μ ≤
        ε n + 2 * Mσ * Real.sqrt t * ∫ ω, Real.sqrt (δ n ω) ∂μ := by
      calc ∫ ω, ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
              (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ∂μ
          ≤ ∫ ω, (δ n ω + 2 * Mσ * Real.sqrt t * Real.sqrt (δ n ω)) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _)
              (hδ_int.add (hsqrtδ_int.const_mul (2 * Mσ * Real.sqrt t)))
              (ae_of_all _ fun ω => h_pw n ω)
        _ = ε n + 2 * Mσ * Real.sqrt t * ∫ ω, Real.sqrt (δ n ω) ∂μ := by
            rw [integral_add hδ_int (hsqrtδ_int.const_mul _), integral_const_mul]
    -- Step 2: E[√δ] ≤ √ε by Jensen (via CS: (∫√δ)² ≤ ∫δ = ε)
    have h_jensen : ∫ ω, Real.sqrt (δ n ω) ∂μ ≤ Real.sqrt (ε n) := by
      have h_nn_int : 0 ≤ ∫ ω, Real.sqrt (δ n ω) ∂μ :=
        integral_nonneg fun ω => Real.sqrt_nonneg _
      suffices hsq : (∫ ω, Real.sqrt (δ n ω) ∂μ) ^ 2 ≤ ε n by
        calc ∫ ω, Real.sqrt (δ n ω) ∂μ
            = Real.sqrt ((∫ ω, Real.sqrt (δ n ω) ∂μ) ^ 2) :=
              (Real.sqrt_sq h_nn_int).symm
          _ ≤ Real.sqrt (ε n) := Real.sqrt_le_sqrt hsq
      -- Use sq_integral_abs_le_integral_sq with g = √δ
      -- (∫|√δ|)² ≤ ∫(√δ)² = ∫δ = ε
      have h_sq_sqrt_eq : ∀ ω, Real.sqrt (δ n ω) ^ 2 = δ n ω :=
        fun ω => Real.sq_sqrt (hδ_nn ω)
      have hcs := sq_integral_abs_le_integral_sq hsqrtδ_int
        (hδ_int.congr (ae_of_all _ fun ω => (h_sq_sqrt_eq ω).symm))
      -- hcs: (∫|√δ|)² ≤ ∫(√δ)²
      -- Convert: |√δ| = √δ (non-negative), (√δ)² = δ
      have h_abs_sqrt : ∫ ω, |Real.sqrt (δ n ω)| ∂μ = ∫ ω, Real.sqrt (δ n ω) ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω => abs_of_nonneg (Real.sqrt_nonneg _))
      have h_sq_eq : ∫ ω, Real.sqrt (δ n ω) ^ 2 ∂μ = ε n :=
        integral_congr_ae (ae_of_all _ fun ω => h_sq_sqrt_eq ω)
      rw [h_abs_sqrt, h_sq_eq] at hcs; exact hcs
    have h_mul : 2 * Mσ * Real.sqrt t * ∫ ω, Real.sqrt (δ n ω) ∂μ ≤
        2 * Mσ * Real.sqrt t * Real.sqrt (ε n) :=
      mul_le_mul_of_nonneg_left h_jensen (by positivity)
    linarith
  -- Squeeze to 0
  have h_upper_tends : Tendsto (fun n => ε n + 2 * Mσ * Real.sqrt t * Real.sqrt (ε n))
      atTop (nhds 0) := by
    have h_sqrt_ε : Tendsto (fun n => Real.sqrt (ε n)) atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hL2_int
      rwa [Function.comp_def, Real.sqrt_zero] at this
    have : (0 : ℝ) = 0 + 2 * Mσ * Real.sqrt t * 0 := by ring
    rw [this]
    exact hL2_int.add (h_sqrt_ε.const_mul _)
  exact squeeze_zero
    (fun n => integral_nonneg fun ω => norm_nonneg _)
    h_upper
    h_upper_tends

/-! ## Simple process integrability infrastructure -/

/-- The time integral of a simple process squared is integrable on [0,t].
    Uses the finite sum decomposition from `valueAtTime_sq_integral_eq_sum`. -/
private lemma simple_process_sq_integral_integrable {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => ∫ s in Set.Icc 0 t, (H.valueAtTime s ω) ^ 2 ∂volume) μ := by
  -- Rewrite using the finite sum decomposition
  have h_eq : (fun ω => ∫ s in Set.Icc 0 t, (H.valueAtTime s ω) ^ 2 ∂volume) =
      (fun ω => ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
        (H.values i ω) ^ 2 * (min (H.times ⟨i + 1, h⟩) t - min (H.times i) t)
      else 0) := by
    ext ω; exact SimpleProcess.valueAtTime_sq_integral_eq_sum H hH_times_nn t ht ω
  rw [h_eq]
  apply integrable_finset_sum _ fun i _ => ?_
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    have h_meas : Measurable (H.values i) :=
      (hH_adapted i).mono (W.F.le_ambient _) le_rfl
    obtain ⟨Ci, hCi⟩ := hH_bdd i
    exact ((integrable_const (Ci ^ 2 * |min (H.times ⟨i + 1, hi⟩) t - min (H.times i) t|)).mono'
      ((h_meas.pow_const 2).aestronglyMeasurable.mul_const _)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hCi ω) 2)
          (abs_nonneg _)))
  · simp only [dif_neg hi]; exact integrable_zero _ _ _

/-- The time integral of a simple process squared is integrable on [s,t]. -/
private lemma simple_process_sq_interval_integrable {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => ∫ u in Set.Icc s t,
      (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) μ := by
  have ht := le_trans hs hst
  -- Express ∫_{s}^{t} = ∫₀^{t} - ∫₀^{s} using setIntegral_Icc_split'
  have h_split : (fun ω => ∫ u in Set.Icc s t,
      (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) =
      (fun ω => ∫ u in Set.Icc 0 t,
        (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) -
      (fun ω => ∫ u in Set.Icc 0 s,
        (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) := by
    ext ω; simp only [Pi.sub_apply]
    obtain ⟨C, hC_nn, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded H hH_bdd
    have h_time_int : IntegrableOn (fun u => (H.valueAtTime u ω) ^ 2)
        (Set.Icc 0 t) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) t)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      have h_val_meas : Measurable (fun u => H.valueAtTime u ω) :=
        (SimpleProcess.valueAtTime_jointly_measurable H).comp
          (measurable_id.prodMk measurable_const)
      exact (integrable_const (C ^ 2)).mono'
        ((h_val_meas.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun u => by
          have hnn : (0 : ℝ) ≤ (H.valueAtTime u ω) ^ 2 := sq_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          calc (H.valueAtTime u ω) ^ 2
              = |H.valueAtTime u ω| ^ 2 := (sq_abs _).symm
            _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC u ω) 2)
    linarith [setIntegral_Icc_split' hs hst h_time_int]
  rw [h_split]
  exact (simple_process_sq_integral_integrable H W hH_adapted hH_bdd hH_times_nn t ht).sub
    (simple_process_sq_integral_integrable H W hH_adapted hH_bdd hH_times_nn s hs)

/-- SI²(t) is integrable for simple processes. -/
private lemma simple_stochasticIntegral_at_sq_integrable {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (H.stochasticIntegral_at W t ω) ^ 2) μ := by
  have h := SimpleProcess.stochasticIntegral_at_sub_sq_integrable H W hH_adapted hH_bdd hH_times_nn
    (fun _ => 0) (integrable_const 0)
    ((integrable_zero _ _ _).congr (ae_of_all _ fun _ => (zero_pow two_ne_zero).symm)) t ht
  simp only [sub_zero] at h; exact h

/-! ## Simple process compensated square set-integral -/

/-- For a simple process H, the compensated square set-integral vanishes:
    ∫_A [SI_H(t₂)² - SI_H(s₂)² - ∫_{s₂}^{t₂} H²] = 0 for A ∈ F_{s₂}.

    This is the simple process version of the conditional Itô isometry.
    The proof uses:
    1. Cross-term vanishing: ∫_A SI(s₂)·(SI(t₂)-SI(s₂)) = 0
       (from `stochasticIntegral_at_martingale`)
    2. BM compensated square: ∫_A [(ΔW)²-Δτ] = 0
       (from independence of BM increments)
    3. Expansion of (SI(t₂)-SI(s₂))² into diagonal + cross terms -/
theorem simple_compensated_sq_setIntegral_zero {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |(H.values i ω)| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s₂ t₂ : ℝ) (hs₂ : 0 ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (A : Set Ω) (hA : @MeasurableSet Ω (W.F.σ_algebra s₂) A) :
    ∫ ω in A, ((H.stochasticIntegral_at W t₂ ω)^2 -
               (H.stochasticIntegral_at W s₂ ω)^2 -
               ∫ u in Icc s₂ t₂, (H.valueAtTime u ω)^2 ∂volume) ∂μ = 0 := by
  sorry -- Key infrastructure: will prove via telescoping + one-step argument

/-! ## Main conditional isometry theorem -/

/-- **Conditional Itô isometry**: For A ∈ F_s with s ≤ s₂ ≤ t₂,
    ∫_A [(SI(t₂)-SI(s₂))² - ∫_{s₂}^{t₂} σ²] dμ = 0.

    Equivalently: ∫_A (SI(t₂)-SI(s₂))² = ∫_A ∫_{s₂}^{t₂} σ².

    **Proof**: L² limit from simple process approximations.
    For each approximation Hₙ, the simple process version holds by
    `simple_compensated_sq_setIntegral_zero`. The convergence uses
    L¹ convergence of the compensated square. -/
theorem ItoProcess.compensated_sq_setIntegral_zero {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s₂ t₂ : ℝ) (hs₂ : 0 ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s₂) A) :
    ∫ ω in A, ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
               ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  -- Step 1: Decompose (SI(t₂)-SI(s₂))² = SI(t₂)² - SI(s₂)² on sets
  -- by the cross-term vanishing (already proved)
  have h_sq_diff := X.setIntegral_sq_increment_eq_diff s₂ t₂ hs₂ hst₂ A hA
  -- Rewrite: ∫_A [(SI(t₂)-SI(s₂))² - ∫σ²] = ∫_A SI(t₂)² - ∫_A SI(s₂)² - ∫_A ∫σ²
  have ht₂ := le_trans hs₂ hst₂
  have hSI_t₂_sq_int := X.stoch_integral_sq_integrable t₂ ht₂
  have hSI_s₂_sq_int := X.stoch_integral_sq_integrable s₂ hs₂
  have hQ_s₂t₂_int := diffusion_sq_interval_integrable X s₂ t₂ hs₂ hst₂
  suffices h : ∫ ω in A, (X.stoch_integral t₂ ω) ^ 2 ∂μ -
      ∫ ω in A, (X.stoch_integral s₂ ω) ^ 2 ∂μ =
      ∫ ω in A, (∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ by
    rw [integral_sub (si_increment_sq_integrable' X s₂ t₂ hs₂ hst₂).integrableOn
      hQ_s₂t₂_int.integrableOn, h_sq_diff]
    linarith
  -- Step 2: Get approximation sequence
  obtain ⟨approx, hadapted, hbdd, hnn, hL2, _, hL2_int⟩ := X.stoch_integral_is_L2_limit
  -- Step 3: For each n, simple_compensated_sq_setIntegral_zero gives the identity
  -- ∫_A SI_n(t₂)² - ∫_A SI_n(s₂)² = ∫_A ∫_{s₂}^{t₂} H_n²
  -- Bridge filtration: F ≤ BM.F
  have hA' : @MeasurableSet Ω (X.BM.F.σ_algebra s₂) A := X.F_le_BM_F s₂ A hA
  have h_simple_id : ∀ n,
      ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω) ^ 2 ∂μ -
      ∫ ω in A, ((approx n).stochasticIntegral_at X.BM s₂ ω) ^ 2 ∂μ =
      ∫ ω in A, (∫ u in Icc s₂ t₂,
        (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) ∂μ := by
    intro n
    have h0 := simple_compensated_sq_setIntegral_zero (approx n) X.BM
      (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂ A hA'
    -- h0: ∫_A [SI_n(t₂)² - SI_n(s₂)² - ∫H_n²] = 0
    -- Split via linearity: ∫_A (a-b-c) = ∫_A a - ∫_A b - ∫_A c = 0
    have hSIn_t₂_sq : Integrable (fun ω =>
        ((approx n).stochasticIntegral_at X.BM t₂ ω) ^ 2) μ :=
      simple_stochasticIntegral_at_sq_integrable _ X.BM
        (hadapted n) (hbdd n) (hnn n) t₂ ht₂
    have hSIn_s₂_sq : Integrable (fun ω =>
        ((approx n).stochasticIntegral_at X.BM s₂ ω) ^ 2) μ :=
      simple_stochasticIntegral_at_sq_integrable _ X.BM
        (hadapted n) (hbdd n) (hnn n) s₂ hs₂
    have hHn_int : Integrable (fun ω =>
        ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) μ :=
      simple_process_sq_interval_integrable _ X.BM
        (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂
    -- Split using integral_sub (forward, not rewrite)
    have h_split_ab : ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 -
        (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2) ∂μ =
        ∫ ω in A, (approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 ∂μ -
        ∫ ω in A, (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2 ∂μ :=
      integral_sub hSIn_t₂_sq.integrableOn hSIn_s₂_sq.integrableOn
    have h_split_abc : ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 -
        (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2 -
        ∫ u in Icc s₂ t₂, (approx n).valueAtTime u ω ^ 2 ∂volume) ∂μ =
        ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 -
          (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2) ∂μ -
        ∫ ω in A, ∫ u in Icc s₂ t₂, (approx n).valueAtTime u ω ^ 2 ∂volume ∂μ :=
      integral_sub (hSIn_t₂_sq.sub hSIn_s₂_sq).integrableOn hHn_int.integrableOn
    linarith
  -- Step 4: Pass to limit using L¹ convergence of SI² and ∫H²
  -- ∫_A SI_n(t₂)² → ∫_A SI(t₂)², ∫_A SI_n(s₂)² → ∫_A SI(s₂)²
  -- ∫_A ∫H_n² → ∫_A ∫σ²
  -- These follow from L¹ convergence (sq_L1_tendsto_of_L2, diffusion_integral_L1_tendsto)
  -- applied with |∫_A (f_n-f)| ≤ ∫ ‖f_n-f‖ → 0
  sorry

/-! ## Squared Orthogonality -/

/-- Compensated squared SI increments on disjoint intervals are orthogonal:
    E[((SI(t₁)-SI(s₁))² - ∫σ²₁) · ((SI(t₂)-SI(s₂))² - ∫σ²₂)] = 0
    for t₁ ≤ s₂.

    **Proof**: Decompose E[Z₁·Z₂] = E[Δ₁²·Z₂] - E[Q₁·Z₂].
    - E[Δ₁²·Z₂] = 0: Δ₁² is F_{s₂}-measurable, conditional isometry gives ∫_A Z₂ = 0.
    - E[Q₁·Z₂] = 0: Approximate Q₁ by F_{s₂}-measurable Q₁ₙ from simple processes. -/
theorem ItoProcess.stoch_integral_squared_orthogonal {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₁ t₁ s₂ t₂ : ℝ)
    (hs₁ : 0 ≤ s₁) (hst₁ : s₁ ≤ t₁) (ht₁s₂ : t₁ ≤ s₂) (hst₂ : s₂ ≤ t₂) :
    ∫ ω, ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
           ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
          ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
           ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  -- Convenience abbreviations and basic facts
  set Z₂ := fun ω => (X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
    ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume
  have hs₂ : 0 ≤ s₂ := le_trans (le_trans hs₁ hst₁) ht₁s₂
  have ht₁ : 0 ≤ t₁ := le_trans hs₁ hst₁
  -- Integrability
  have hΔ₁_sq_int := si_increment_sq_integrable' X s₁ t₁ hs₁ hst₁
  have hQ₁_int := diffusion_sq_interval_integrable X s₁ t₁ hs₁ hst₁
  have hZ₂_int := compensated_sq_integrable' X s₂ t₂ hs₂ hst₂
  have hZ₂_sq_int := compensated_sq_sq_integrable' X hMσ s₂ t₂ hs₂ hst₂
  have hΔ₁_L4 := stoch_integral_increment_L4_integrable_proof X hMσ s₁ t₁ hs₁ hst₁
  have hQ₁_bdd := diffusion_sq_integral_bound X hMσ s₁ t₁ hs₁ hst₁
  -- Δ₁²·Z₂ integrable (AM-GM: |ab| ≤ a² + b², Δ₁⁴ and Z₂² integrable)
  have hΔ₁_sq_Z₂_int : Integrable (fun ω =>
      (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω) μ := by
    have hdom : Integrable (fun ω =>
        (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2) μ :=
      hΔ₁_L4.add hZ₂_sq_int
    exact hdom.mono'
      (hΔ₁_sq_int.aestronglyMeasurable.mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω))]
        have h4eq : (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 =
            ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2) ^ 2 := by ring
        rw [h4eq]
        nlinarith [sq_nonneg ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 - |Z₂ ω|),
          sq_abs (Z₂ ω)])
  -- Q₁·Z₂ integrable (Q₁ bounded, Z₂ integrable)
  have hQ₁_Z₂_int : Integrable (fun ω =>
      (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω) μ := by
    set C₁ := Mσ ^ 2 * (t₁ - s₁)
    -- Dominate by C₁ * ‖Z₂‖
    exact (hZ₂_int.norm.const_mul C₁).mono'
      (hQ₁_int.aestronglyMeasurable.mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hQ₁_bdd ω) (abs_nonneg _))
  -- Step 1: Decompose ∫ (Δ₁²-Q₁)·Z₂ = ∫ Δ₁²·Z₂ - ∫ Q₁·Z₂
  have hdecomp : (fun ω => ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
      ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
      ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
       ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume)) =
      (fun ω => (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω -
        (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω) := by
    ext ω; ring
  rw [hdecomp, integral_sub hΔ₁_sq_Z₂_int hQ₁_Z₂_int]
  -- Step 2: E[Δ₁²·Z₂] = 0 by martingale orthogonality + conditional isometry
  have h_part1 : ∫ ω, (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω ∂μ = 0 := by
    apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
    · -- Δ₁² is F_{s₂}-measurable: SI(t₁), SI(s₁) are F_{t₁}-meas, t₁ ≤ s₂
      exact ((X.stoch_integral_adapted t₁).sub
        ((X.stoch_integral_adapted s₁).mono (F.mono s₁ t₁ hst₁) le_rfl)).pow_const 2
        |>.mono (F.mono t₁ s₂ ht₁s₂) le_rfl
    · exact hZ₂_int
    · exact hΔ₁_sq_Z₂_int
    · -- Conditional isometry: ∫_A Z₂ = 0 for A ∈ F_{s₂}
      exact X.compensated_sq_setIntegral_zero s₂ t₂ hs₂ hst₂
  -- Step 3: E[Q₁·Z₂] = 0 by approximation
  have h_part2 : ∫ ω, (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω ∂μ = 0 := by
    sorry
  linarith

end SPDE

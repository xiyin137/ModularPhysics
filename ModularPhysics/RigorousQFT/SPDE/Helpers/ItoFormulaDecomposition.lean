/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.StochasticIntegration
import ModularPhysics.RigorousQFT.SPDE.Helpers.ItoFormulaInfrastructure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Itô Formula Decomposition Infrastructure

Sub-lemmas for the Itô formula L² convergence proof.

## Key results

1. `integral_mul_eq_zero_of_setIntegral_eq_zero` — Martingale orthogonality
2. `simple_bilinear_isometry_different_times` — E[S(t)·S(s)] = E[S(s)²]
3. `stoch_integral_increment_L2_bound` — E[|SI(t) - SI(s)|²] ≤ Mσ²·(t-s)
4. `ito_process_increment_L2_bound` — E[|X(t)-X(s)|²] ≤ C·(t-s)
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

variable {Ω : Type*} [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Square integrability of simple stochastic integrals -/

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-- Simple stochastic integrals of bounded adapted processes are square-integrable. -/
theorem stochasticIntegral_at_sq_integrable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (H.stochasticIntegral_at W t ω) ^ 2) μ := by
  have h := stochasticIntegral_at_sub_sq_integrable H W hH_adapted hH_bdd hH_times_nn
    (fun _ => 0) (integrable_const 0) (by simp) t ht
  simp only [sub_zero] at h; exact h

/-- Simple stochastic integrals at time s are measurable w.r.t. the filtration at time s.
    Uses the min-capped reformulation: S(s) = Σ Hᵢ·ΔWᵢ_cap(s) where each summand
    only involves BM values at times ≤ s. -/
theorem stochasticIntegral_at_filtration_measurable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (_hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s : ℝ) (_hs : 0 ≤ s) :
    @Measurable Ω ℝ (W.F.σ_algebra s) _ (H.stochasticIntegral_at W s) := by
  -- Rewrite as min-capped form
  have heq : H.stochasticIntegral_at W s = fun ω =>
      ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
        H.values i ω * (W.process (min (H.times ⟨i + 1, h⟩) s) ω -
                         W.process (min (H.times i) s) ω)
      else 0 := by
    ext ω; exact H.stochasticIntegral_at_eq_min W s ω
  rw [heq]
  -- Sum of measurable functions is measurable
  apply Finset.measurable_sum
  intro i _
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    by_cases hts : H.times i ≤ s
    · -- t_i ≤ s: H_i is F_{t_i}-meas ≤ F_s, BM values at times ≤ s are F_s-meas
      exact ((hH_adapted i).mono (W.F.mono _ _ hts) le_rfl).mul
        (((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_right _ _)) le_rfl).sub
         ((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_right _ _)) le_rfl))
    · -- t_i > s: increment = W(s)-W(s) = 0, so product = 0
      push_neg at hts
      have h1 : min (H.times i) s = s := min_eq_right (le_of_lt hts)
      have h2 : min (H.times ⟨i + 1, hi⟩) s = s :=
        min_eq_right (le_trans (le_of_lt hts)
          (le_of_lt (H.increasing i ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))))
      have : (fun ω => H.values i ω * (W.process (min (H.times ⟨i + 1, hi⟩) s) ω -
                         W.process (min (H.times i) s) ω)) = fun _ => 0 := by
        ext ω; rw [h1, h2, sub_self, mul_zero]
      rw [this]; exact measurable_const
  · simp only [dif_neg hi]; exact measurable_const

end SimpleProcess

/-! ## Martingale orthogonality via conditional expectation

If ∫_A Y = 0 for all A ∈ m, and X is m-measurable, Y integrable, X*Y integrable,
then ∫ X·Y = 0. Proof: condExp m μ Y = 0 a.e. → condExp m μ (X·Y) = X · 0 = 0 a.e.
→ ∫ X·Y = ∫ condExp(X·Y) = 0. -/

/-- Martingale orthogonality: if ∫_A Y = 0 for all A ∈ m, X is m-measurable,
    and X·Y is integrable, then ∫ X·Y = 0. -/
theorem integral_mul_eq_zero_of_setIntegral_eq_zero
    {m : MeasurableSpace Ω}
    (hm : m ≤ instΩ)
    {X Y : Ω → ℝ}
    (hX_meas : @Measurable Ω ℝ m _ X)
    (hY_int : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ)
    [IsProbabilityMeasure μ]
    (hset : ∀ A : Set Ω, @MeasurableSet Ω m A → ∫ ω in A, Y ω ∂μ = 0) :
    ∫ ω, X ω * Y ω ∂μ = 0 := by
  -- SigmaFinite (μ.trim hm) holds since μ is a probability measure
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  -- Step 1: condExp m μ Y = 0 a.e.
  -- Use uniqueness: 0 satisfies the defining property of condExp m μ Y
  have hcondY0 : (0 : Ω → ℝ) =ᵐ[μ] μ[Y | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hY_int
    · intro s _ _; exact integrableOn_zero
    · intro s hs _
      simp only [Pi.zero_apply, integral_zero]
      exact (hset s hs).symm
    · exact aestronglyMeasurable_zero
  have hcondY : μ[Y | m] =ᵐ[μ] (0 : Ω → ℝ) := hcondY0.symm
  -- Step 2: condExp m μ (X·Y) =ᵐ X · condExp m μ Y =ᵐ 0
  have hX_asm : AEStronglyMeasurable[m] X μ :=
    (hX_meas.stronglyMeasurable).aestronglyMeasurable
  -- Pull-out: μ[X * Y | m] =ᵐ X * μ[Y | m]
  have hXY_eq : (fun ω => X ω * Y ω) = X * Y := rfl
  have hpull : μ[X * Y | m] =ᵐ[μ] X * μ[Y | m] :=
    condExp_mul_of_aestronglyMeasurable_left hX_asm (by rwa [← hXY_eq]) hY_int
  -- X * condExp Y =ᵐ X * 0 = 0
  have hXcond0 : X * μ[Y | m] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [hcondY] with ω hω
    simp only [Pi.mul_apply, Pi.zero_apply, hω, mul_zero]
  have hcond0 : μ[X * Y | m] =ᵐ[μ] (0 : Ω → ℝ) := hpull.trans hXcond0
  -- Step 3: ∫ X·Y = ∫ condExp(X·Y) = ∫ 0 = 0
  calc ∫ ω, X ω * Y ω ∂μ
      = ∫ ω, (X * Y) ω ∂μ := by rfl
    _ = ∫ ω, μ[X * Y | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂μ := integral_congr_ae hcond0
    _ = 0 := by simp

/-! ## Bilinear isometry at different times -/

/-- E[S(t)·S(s)] = E[S(s)²] for s ≤ t. The increment S(t)-S(s) is orthogonal
    to S(s) by the martingale property and the orthogonality lemma. -/
theorem simple_bilinear_isometry_different_times
    {F : Filtration Ω ℝ} (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (H.stochasticIntegral_at W t ω) * (H.stochasticIntegral_at W s ω) ∂μ =
    ∫ ω, (H.stochasticIntegral_at W s ω)^2 ∂μ := by
  -- S(t) = S(s) + (S(t)-S(s)), so S(t)·S(s) = S(s)² + (S(t)-S(s))·S(s)
  have hdecomp : ∀ ω, H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω =
      (H.stochasticIntegral_at W s ω) ^ 2 +
      (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
       H.stochasticIntegral_at W s ω := by
    intro ω; ring
  simp_rw [hdecomp]
  -- Integrability
  have hS_s_int : Integrable (H.stochasticIntegral_at W s) μ :=
    SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  have hS_t_int : Integrable (H.stochasticIntegral_at W t) μ :=
    SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
  have hS_sq_int : Integrable (fun ω => (H.stochasticIntegral_at W s ω) ^ 2) μ :=
    SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  -- Cross term integrability: (S(t)-S(s))·S(s) integrable via AM-GM bound
  have hcross_int : Integrable (fun ω =>
      (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
      H.stochasticIntegral_at W s ω) μ := by
    have hSt_sq := SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
    apply Integrable.mono' ((hSt_sq.add hS_sq_int).add hS_sq_int)
    · exact (hS_t_int.sub hS_s_int).aestronglyMeasurable.mul hS_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      set a := H.stochasticIntegral_at W t ω
      set b := H.stochasticIntegral_at W s ω
      rw [abs_mul]
      nlinarith [sq_abs (a - b), sq_abs b, sq_abs a, sq_nonneg (|a - b| - |b|)]
  rw [integral_add hS_sq_int hcross_int]
  -- Suffices to show cross term = 0
  suffices hcross : ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
      H.stochasticIntegral_at W s ω ∂μ = 0 by linarith
  -- Rewrite as ∫ S(s) · (S(t)-S(s)) by commutativity
  have hcomm : (fun ω => (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
      H.stochasticIntegral_at W s ω) =
      (fun ω => H.stochasticIntegral_at W s ω *
      (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω)) := by
    ext ω; ring
  rw [hcomm]
  -- Apply orthogonality: S(s) is F_s-measurable, S(t)-S(s) has zero set-integrals
  apply integral_mul_eq_zero_of_setIntegral_eq_zero (W.F.le_ambient s)
  · -- S(s) is F_s-measurable
    exact SimpleProcess.stochasticIntegral_at_filtration_measurable H W hH_adapted hH_times_nn s hs
  · -- S(t)-S(s) is integrable
    exact hS_t_int.sub hS_s_int
  · -- S(s)·(S(t)-S(s)) is integrable
    rw [← hcomm]; exact hcross_int
  · -- ∫_A (S(t)-S(s)) = 0 for all A ∈ F_s (martingale property)
    intro A hA
    rw [integral_sub (hS_t_int.integrableOn) (hS_s_int.integrableOn)]
    exact sub_eq_zero.mpr
      (SimpleProcess.stochasticIntegral_at_martingale H W hH_adapted hH_bdd hH_times_nn s t hs hst A hA)

/-- E[|S(t)-S(s)|²] = E[S(t)²] - E[S(s)²] for s ≤ t. -/
theorem simple_increment_L2 {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω)^2 ∂μ =
    ∫ ω, (H.stochasticIntegral_at W t ω)^2 ∂μ -
    ∫ ω, (H.stochasticIntegral_at W s ω)^2 ∂μ := by
  -- Integrability
  have hS_s_int := SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  have hS_t_int := SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
  have hS_s_sq := SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  have hS_t_sq := SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
  -- Product S_t * S_s is integrable (|ab| ≤ (a²+b²)/2)
  have hprod_int : Integrable (fun ω =>
      H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω) μ := by
    apply Integrable.mono' (hS_t_sq.add hS_s_sq)
    · exact hS_t_int.aestronglyMeasurable.mul hS_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_mul]
      nlinarith [sq_abs (H.stochasticIntegral_at W t ω),
        sq_abs (H.stochasticIntegral_at W s ω),
        sq_nonneg (|H.stochasticIntegral_at W t ω| - |H.stochasticIntegral_at W s ω|)]
  -- Bilinear isometry: E[S_t·S_s] = E[S_s²]
  have hbil := simple_bilinear_isometry_different_times H W hH_adapted hH_bdd hH_times_nn s t hs hst
  -- Expand (a-b)² = a² + b² - 2ab pointwise, then split the integral
  have h_pw : ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) ^ 2 ∂μ =
      ∫ ω, (H.stochasticIntegral_at W t ω ^ 2 + H.stochasticIntegral_at W s ω ^ 2 -
      2 * (H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω)) ∂μ :=
    integral_congr_ae (ae_of_all _ (fun ω => by ring))
  -- Split integrals using have lemmas (avoids rw pattern-matching issues)
  have h_sub := integral_sub (hS_t_sq.add hS_s_sq) (hprod_int.const_mul 2)
  have h_add := integral_add hS_t_sq hS_s_sq
  have h_mul := integral_const_mul (μ := μ) (2 : ℝ)
    (fun ω => H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω)
  -- Normalize function-level to value-level
  simp only [Pi.add_apply] at h_sub h_add
  -- Chain: ∫(a-b)² = ∫(a²+b²-2ab) = (∫a²+∫b²) - 2∫(ab) = ∫a²+∫b²-2∫b² = ∫a²-∫b²
  linarith

/-! ## Stochastic integral increment L² bound -/

/-- E[|SI(t) - SI(s)|²] ≤ Mσ² · (t - s) for ItoProcess with bounded diffusion. -/
theorem stoch_integral_increment_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω)^2 ∂μ ≤
    Mσ^2 * (t - s) := by
  sorry

/-! ## Process increment moment bounds -/

/-- E[|X(t) - X(s)|²] ≤ C · (t - s) for bounded coefficients. -/
theorem ito_process_increment_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (hdt : t - s ≤ 1) :
    ∫ ω, (X.process t ω - X.process s ω)^2 ∂μ ≤
    (2 * Mμ^2 + 2 * Mσ^2) * (t - s) := by
  sorry

/-- E[|X(t) - X(s)|⁴] ≤ C · (t - s)² for bounded coefficients. -/
theorem ito_process_increment_L4_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (hdt : t - s ≤ 1) :
    ∫ ω, (X.process t ω - X.process s ω)^4 ∂μ ≤
    (8 * Mμ^4 + 8 * 3 * Mσ^4) * (t - s)^2 := by
  sorry

/-! ## Riemann sum and Taylor remainder convergence -/

/-- Riemann sum L² convergence for bounded adapted processes. -/
theorem riemann_sum_L2_convergence
    [IsProbabilityMeasure μ]
    (g : ℝ → Ω → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hg_bdd : ∀ s ω, |g s ω| ≤ C)
    (_hg_meas : ∀ s, Measurable (g s))
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1)) -
         ∫ s in Set.Icc 0 t, g s ω ∂volume)^2 ∂μ)
      atTop (nhds 0) := by
  sorry

/-- Taylor remainder L² convergence summed over partition intervals. -/
theorem taylor_remainder_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (_hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mμ : ℝ} (_hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (_hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    {Mf'' : ℝ} (_hMf'' : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf'')
    (t : ℝ) (_ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (f (↑(i : ℕ) * t / ↑(n + 1))
             (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω) -
           f (↑(i : ℕ) * t / ↑(n + 1))
             (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) -
           deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x)
             (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
             (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
              X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) -
           (1 : ℝ) / 2 *
             deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
               (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
             (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
              X.process (↑(i : ℕ) * t / ↑(n + 1)) ω)^2))^2 ∂μ)
      atTop (nhds 0) := by
  sorry

end SPDE

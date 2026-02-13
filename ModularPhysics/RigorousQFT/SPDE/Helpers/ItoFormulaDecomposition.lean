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
  -- Step 1: Apply the Itô isometry bound from ItoProcess
  have hqv := X.stoch_integral_qv_bound s t hs hst
  -- Step 2: Bound E[σ(u)²] ≤ Mσ² for each u
  have hσ_sq_bdd : ∀ u, ∫ ω, (X.diffusion u ω) ^ 2 ∂μ ≤ Mσ ^ 2 := by
    intro u
    have h1 : ∫ ω, (X.diffusion u ω) ^ 2 ∂μ ≤ ∫ ω, Mσ ^ 2 ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun ω => sq_nonneg _
      · exact integrable_const _
      · exact ae_of_all _ fun ω =>
          sq_le_sq' (abs_le.mp (hMσ u ω)).1 (abs_le.mp (hMσ u ω)).2
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h1
    exact h1
  -- Step 3: Bound ∫_[s,t] E[σ²] du ≤ Mσ² · (t - s)
  -- Use integral_mono_of_nonneg on restricted measure (doesn't need f measurable)
  calc ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ
      ≤ ∫ u in Set.Icc s t, (∫ ω, (X.diffusion u ω) ^ 2 ∂μ) ∂volume := hqv
    _ ≤ ∫ u in Set.Icc s t, Mσ ^ 2 ∂volume := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun u => integral_nonneg (fun ω => sq_nonneg _)
        · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        · exact ae_of_all _ fun u => hσ_sq_bdd u
    _ = Mσ ^ 2 * (t - s) := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hst), smul_eq_mul]
        ring

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
  -- Abbreviations
  set D : Ω → ℝ := fun ω =>
    ∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
    ∫ u in Set.Icc 0 s, X.drift u ω ∂volume with hD_def
  set S : Ω → ℝ := fun ω => X.stoch_integral t ω - X.stoch_integral s ω with hS_def
  -- Step 1: X(t) - X(s) = D + S a.e.
  have hdecomp : ∀ᵐ ω ∂μ, X.process t ω - X.process s ω = D ω + S ω := by
    filter_upwards [X.integral_form t (le_trans hs hst), X.integral_form s hs] with ω hωt hωs
    simp only [D, S]; linarith
  -- Step 2: Pointwise drift bound |D(ω)| ≤ Mμ·(t-s)
  have hD_bdd : ∀ ω, |D ω| ≤ Mμ * (t - s) := by
    intro ω
    have hint_t : IntegrableOn (fun u => X.drift u ω) (Set.Icc 0 t) volume :=
      X.drift_time_integrable ω t (le_trans hs hst)
    -- D(ω) = ∫_{Icc 0 t \ Icc 0 s} drift u ω dv
    have hD_eq : D ω = ∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume :=
      (integral_diff measurableSet_Icc hint_t (Set.Icc_subset_Icc_right hst)).symm
    rw [hD_eq]
    -- volume(diff) is finite
    have hvol_ne_top : volume (Set.Icc 0 t \ Set.Icc 0 s) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.diff_subset)
    -- |∫_{diff} drift| ≤ Mμ · volume.real(diff)
    have hbnd : ‖∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume‖ ≤
        Mμ * volume.real (Set.Icc 0 t \ Set.Icc 0 s) :=
      norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hvol_ne_top)
        fun u _ => Real.norm_eq_abs _ ▸ hMμ u ω
    rw [Real.norm_eq_abs] at hbnd
    -- volume.real(Icc 0 t \ Icc 0 s) = t - s
    have h_fin_s : volume (Set.Icc 0 s) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hvol_eq : volume.real (Set.Icc 0 t \ Set.Icc 0 s) = t - s := by
      show (volume (Set.Icc 0 t \ Set.Icc 0 s)).toReal = t - s
      rw [measure_diff (Set.Icc_subset_Icc_right hst) measurableSet_Icc.nullMeasurableSet h_fin_s]
      rw [Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero]
      rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_ofReal hst) ENNReal.ofReal_ne_top]
      rw [ENNReal.toReal_ofReal (le_trans hs hst), ENNReal.toReal_ofReal hs]
    rw [hvol_eq] at hbnd; linarith
  -- Step 3: D²(ω) ≤ Mμ²·(t-s)²
  have hD_sq_bdd : ∀ ω, D ω ^ 2 ≤ Mμ ^ 2 * (t - s) ^ 2 := fun ω => by
    have h := abs_le.mp (hD_bdd ω)
    calc D ω ^ 2 ≤ (Mμ * (t - s)) ^ 2 := sq_le_sq' h.1 h.2
      _ = Mμ ^ 2 * (t - s) ^ 2 := by ring
  -- Step 4: D is AEStronglyMeasurable (= X(t)-X(s)-S a.e., which is measurable)
  have hD_asm : AEStronglyMeasurable D μ := by
    have hXt : AEStronglyMeasurable (X.process t) μ :=
      ((X.process_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
    have hXs : AEStronglyMeasurable (X.process s) μ :=
      ((X.process_adapted s).mono (F.le_ambient s) le_rfl).aestronglyMeasurable
    have hSt : AEStronglyMeasurable (X.stoch_integral t) μ :=
      ((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
    have hSs : AEStronglyMeasurable (X.stoch_integral s) μ :=
      ((X.stoch_integral_adapted s).mono (F.le_ambient s) le_rfl).aestronglyMeasurable
    exact ((hXt.sub hXs).sub (hSt.sub hSs)).congr
      (hdecomp.mono fun ω hω => by simp only [D, S, Pi.sub_apply] at hω ⊢; linarith)
  -- Step 5: D² integrable (bounded on probability space)
  have hD_sq_int : Integrable (fun ω => D ω ^ 2) μ :=
    (integrable_const (Mμ ^ 2 * (t - s) ^ 2)).mono' (hD_asm.pow 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hD_sq_bdd ω)
  -- Step 6: S² integrable
  have hS_sq_int : Integrable (fun ω => S ω ^ 2) μ := by
    show Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ
    have hSt_sq := X.stoch_integral_sq_integrable t (le_trans hs hst)
    have hSs_sq := X.stoch_integral_sq_integrable s hs
    exact ((hSt_sq.add hSs_sq).const_mul 2).mono'
      (((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl |>.aestronglyMeasurable).sub
        ((X.stoch_integral_adapted s).mono (F.le_ambient s) le_rfl |>.aestronglyMeasurable)
        |>.pow 2)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (X.stoch_integral t ω + X.stoch_integral s ω)])
  -- Step 7: E[S²] ≤ Mσ²·(t-s)
  have hSI := stoch_integral_increment_L2_bound X hMσ s t hs hst
  -- Step 8: E[D²] ≤ Mμ²·(t-s)²
  have hE_D_sq : ∫ ω, D ω ^ 2 ∂μ ≤ Mμ ^ 2 * (t - s) ^ 2 := by
    calc ∫ ω, D ω ^ 2 ∂μ
        ≤ ∫ ω, (Mμ ^ 2 * (t - s) ^ 2 : ℝ) ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
            (integrable_const _) (ae_of_all _ fun ω => hD_sq_bdd ω)
      _ = Mμ ^ 2 * (t - s) ^ 2 := by
          simp [integral_const, Measure.real, measure_univ, ENNReal.toReal_one]
  -- Step 9: Combine via (a+b)² ≤ 2a² + 2b² and split integrals
  calc ∫ ω, (X.process t ω - X.process s ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * D ω ^ 2 + 2 * S ω ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun ω => sq_nonneg _
        · exact (hD_sq_int.const_mul 2).add (hS_sq_int.const_mul 2)
        · filter_upwards [hdecomp] with ω hω
          rw [hω]; nlinarith [sq_nonneg (D ω - S ω)]
    _ = 2 * ∫ ω, D ω ^ 2 ∂μ + 2 * ∫ ω, S ω ^ 2 ∂μ := by
        rw [integral_add (hD_sq_int.const_mul 2) (hS_sq_int.const_mul 2)]
        rw [integral_const_mul, integral_const_mul]
    _ ≤ 2 * (Mμ ^ 2 * (t - s) ^ 2) + 2 * (Mσ ^ 2 * (t - s)) :=
        add_le_add (mul_le_mul_of_nonneg_left hE_D_sq (by norm_num))
          (mul_le_mul_of_nonneg_left hSI (by norm_num))
    _ ≤ (2 * Mμ ^ 2 + 2 * Mσ ^ 2) * (t - s) := by
        have hts_sq : (t - s) ^ 2 ≤ (t - s) := by nlinarith [sub_nonneg.mpr hst]
        have h := mul_le_mul_of_nonneg_left hts_sq (sq_nonneg Mμ)
        nlinarith

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

/-- Riemann sum L² convergence for bounded continuous-in-time processes.

  For bounded g with |g(s, ω)| ≤ C and continuous s → g(s, ω) for each ω,
  the Riemann sum Σ g(tᵢ, ω) Δt converges to ∫₀ᵗ g(s, ω) ds in L²(Ω). -/
theorem riemann_sum_L2_convergence
    [IsProbabilityMeasure μ]
    (g : ℝ → Ω → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hg_bdd : ∀ s ω, |g s ω| ≤ C)
    (hg_meas : ∀ s, Measurable (g s))
    (t : ℝ) (ht : 0 < t)
    (hg_cont : ∀ ω, ContinuousOn (fun s => g s ω) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1)) -
         ∫ s in Set.Icc 0 t, g s ω ∂volume)^2 ∂μ)
      atTop (nhds 0) := by
  -- Abbreviate the error for readability
  set err : ℕ → Ω → ℝ := fun n ω =>
    ∑ i : Fin (n + 1),
      g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1)) -
    ∫ s in Set.Icc 0 t, g s ω ∂volume
  -- Step 1: error is bounded by 2Ct
  have herr_bdd : ∀ n ω, |err n ω| ≤ 2 * C * t := by
    intro n ω
    -- Sum bound: |Σ g(tᵢ) Δt| ≤ C·t
    have hΔt_nn : (0 : ℝ) ≤ t / (↑(n + 1) : ℝ) := div_nonneg ht.le (Nat.cast_nonneg _)
    have hsum : |∑ i : Fin (n + 1), g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1))| ≤ C * t := by
      calc |∑ i : Fin (n + 1), g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1))|
          ≤ ∑ i : Fin (n + 1), |g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (n + 1), C * (t / ↑(n + 1)) := by
            apply Finset.sum_le_sum; intro i _
            rw [abs_mul, abs_of_nonneg hΔt_nn]
            exact mul_le_mul_of_nonneg_right (hg_bdd _ _) hΔt_nn
        _ = C * t := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            field_simp
    -- Integral bound: |∫ g| ≤ C·t (using norm_setIntegral_le_of_norm_le_const)
    have hvol_ne_top : volume (Set.Icc 0 t) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hint : |∫ s in Set.Icc 0 t, g s ω ∂volume| ≤ C * t := by
      have key : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖g s ω‖ ≤ C :=
        fun s _ => by rw [Real.norm_eq_abs]; exact hg_bdd s ω
      have h := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hvol_ne_top) key
      rw [Real.norm_eq_abs] at h
      have hvol : volume.real (Set.Icc (0 : ℝ) t) = t := by
        simp only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht.le]
      rw [hvol] at h; linarith
    -- Triangle inequality: |a - b| ≤ |a| + |b|
    have htri : |err n ω| ≤
        |∑ i : Fin (n + 1), g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1))| +
        |∫ s in Set.Icc 0 t, g s ω ∂volume| := by
      have := norm_sub_le
        (∑ i : Fin (n + 1), g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1)))
        (∫ s in Set.Icc 0 t, g s ω ∂volume)
      simp only [Real.norm_eq_abs] at this
      exact this
    linarith
  -- Step 2: error² bounded by (2Ct)²
  have herr_sq_bdd : ∀ n ω, (err n ω) ^ 2 ≤ (2 * C * t) ^ 2 := by
    intro n ω
    have h := herr_bdd n ω
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  -- Step 3: error(ω) → 0 for each ω (Riemann sum convergence for continuous functions)
  have herr_ptwise : ∀ ω, Filter.Tendsto (err · ω) atTop (nhds 0) := by
    intro ω
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- g(·, ω) is uniformly continuous on compact [0, t]
    have huc : UniformContinuousOn (fun s => g s ω) (Set.Icc 0 t) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (hg_cont ω)
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / (t + 1)) (div_pos hε (by linarith))
    obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
    refine ⟨N, fun n hn => ?_⟩
    -- For n ≥ N, the mesh t/(n+1) < δ
    have hn1_pos : (0 : ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (by omega)
    have hmesh : t / (↑(n + 1) : ℝ) < δ := by
      rw [div_lt_iff₀ hn1_pos]
      calc t < δ * (↑N + 1) := by
              calc t = (t / δ) * δ := by rw [div_mul_cancel₀ t (ne_of_gt hδ_pos)]
                _ < (↑N + 1) * δ := by nlinarith
                _ = δ * (↑N + 1) := by ring
        _ ≤ δ * ↑(n + 1) := by
              apply mul_le_mul_of_nonneg_left _ hδ_pos.le
              push_cast; linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr (by omega)]
    -- Bound: dist (err n ω) 0 < ε
    rw [Real.dist_eq, sub_zero]
    -- Set up partition function
    set Δ := t / (↑(n + 1) : ℝ) with hΔ_def
    have hΔ_pos : (0 : ℝ) < Δ := div_pos ht hn1_pos
    -- Partition points: ptFn k = k * Δ
    set ptFn : ℕ → ℝ := fun k => ↑k * Δ with hptFn_def
    have hpt0 : ptFn 0 = 0 := by simp [hptFn_def]
    have hptn1 : ptFn (n + 1) = t := by
      simp only [hptFn_def, hΔ_def, Nat.cast_add, Nat.cast_one]
      field_simp
    have hpt_step : ∀ k, ptFn (k + 1) - ptFn k = Δ := by
      intro k; simp only [hptFn_def, Nat.cast_add, Nat.cast_one]; ring
    -- Partition points lie in [0, t]
    have hpt_mem : ∀ k, k ≤ n + 1 → ptFn k ∈ Set.Icc 0 t := by
      intro k hk
      refine ⟨by positivity, ?_⟩
      calc (↑k : ℝ) * Δ ≤ ↑(n + 1) * Δ := by
              apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hΔ_pos.le
        _ = t := by simp [hΔ_def]; field_simp
    -- Subinterval endpoints are ordered
    have hpt_le : ∀ k, ptFn k ≤ ptFn (k + 1) := fun k => by linarith [hpt_step k]
    -- g(·, ω) is interval integrable on each subinterval
    have hg_ii : ∀ k < n + 1, IntervalIntegrable (g · ω) volume (ptFn k) (ptFn (k + 1)) := by
      intro k hk
      apply ContinuousOn.intervalIntegrable_of_Icc (hpt_le k)
      exact (hg_cont ω).mono (Set.Icc_subset_Icc (hpt_mem k (by omega)).1 (hpt_mem (k+1) (by omega)).2)
    -- Convert Set.Icc integral to intervalIntegral
    have hIcc_eq_ii : ∫ s in Set.Icc 0 t, g s ω ∂volume = ∫ s in (0:ℝ)..t, g s ω := by
      rw [intervalIntegral.integral_of_le ht.le]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
    -- Split interval integral into sum over subintervals
    have hsplit : ∫ s in (0:ℝ)..t, g s ω =
        ∑ k ∈ Finset.range (n + 1), ∫ s in (ptFn k)..(ptFn (k + 1)), g s ω := by
      rw [← hpt0, ← hptn1]
      exact (intervalIntegral.sum_integral_adjacent_intervals hg_ii).symm
    -- Express Riemann sum using Finset.range and constant integrals
    have hRS_eq : ∑ i : Fin (n + 1), g (↑↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1)) =
        ∑ k ∈ Finset.range (n + 1), ∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω := by
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1; ext ⟨i, hi⟩
      rw [intervalIntegral.integral_const, smul_eq_mul, hpt_step]
      -- g(↑i * t / ↑(n+1)) ω * Δ = Δ * g(↑i * Δ) ω
      simp only [hptFn_def, hΔ_def, mul_div_assoc]
      ring
    -- Express error as sum of integral differences
    have herr_eq : err n ω =
        ∑ k ∈ Finset.range (n + 1),
          ((∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
           (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω)) := by
      simp only [err, hIcc_eq_ii, hsplit, hRS_eq, ← Finset.sum_sub_distrib]
    -- Bound each term using uniform continuity
    have hterm_bdd : ∀ k ∈ Finset.range (n + 1),
        |(∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
         (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω)| ≤ ε / (t + 1) * Δ := by
      intro k hk
      rw [Finset.mem_range] at hk
      -- Combine integrals: ∫ c - ∫ f = ∫ (c - f)
      rw [← intervalIntegral.integral_sub intervalIntegrable_const (hg_ii k hk)]
      -- Apply norm bound for interval integrals
      have hle : ‖∫ s in (ptFn k)..(ptFn (k + 1)), (g (ptFn k) ω - g s ω)‖ ≤
          ε / (t + 1) * |ptFn (k + 1) - ptFn k| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le (hpt_le k)] at hs
        rw [Real.norm_eq_abs]
        -- Need |g(ptFn k, ω) - g(s, ω)| ≤ ε / (t + 1)
        have hsk : ptFn k ∈ Set.Icc 0 t := hpt_mem k (by omega)
        have hs_mem : s ∈ Set.Icc 0 t := by
          constructor
          · linarith [hsk.1, hs.1]
          · exact le_trans hs.2 (hpt_mem (k + 1) (by omega)).2
        have hdist : dist (ptFn k) s < δ := by
          rw [Real.dist_eq]
          calc |ptFn k - s| = s - ptFn k := by
                  rw [abs_of_nonpos (by linarith [hs.1])]
                  ring
            _ ≤ ptFn (k + 1) - ptFn k := by linarith [hs.2]
            _ = Δ := hpt_step k
            _ < δ := hmesh
        exact le_of_lt (hδ (ptFn k) hsk s hs_mem hdist)
      rw [Real.norm_eq_abs] at hle
      calc |(∫ s in (ptFn k)..(ptFn (k + 1)), (g (ptFn k) ω - g s ω))|
          ≤ ε / (t + 1) * |ptFn (k + 1) - ptFn k| := hle
        _ = ε / (t + 1) * Δ := by
            rw [hpt_step, abs_of_pos hΔ_pos]
    -- Final bound: sum of (ε/(t+1)) * Δ over (n+1) terms = ε * t / (t+1) < ε
    calc |err n ω|
        = |∑ k ∈ Finset.range (n + 1),
            ((∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
             (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω))| := by rw [herr_eq]
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            |(∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
             (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), ε / (t + 1) * Δ :=
          Finset.sum_le_sum hterm_bdd
      _ = ↑(n + 1) * (ε / (t + 1) * Δ) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ε * (t / (t + 1)) := by
          simp only [hΔ_def]; field_simp
      _ < ε * 1 := by
          apply mul_lt_mul_of_pos_left _ hε
          rw [div_lt_one (by linarith : (0:ℝ) < t + 1)]
          linarith
      _ = ε := mul_one ε
  -- Step 4: error²(ω) → 0 for each ω
  have herr_sq_ptwise : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (err n ω) ^ 2) atTop (nhds 0) := by
    filter_upwards with ω
    rw [show (0 : ℝ) = 0 ^ 2 from by norm_num]
    exact (herr_ptwise ω).pow 2
  -- Step 5: error² is AEStronglyMeasurable
  have herr_sq_meas : ∀ n, AEStronglyMeasurable (fun ω => (err n ω) ^ 2) μ := by
    intro n
    have hsum_meas : Measurable (fun ω => ∑ i : Fin (n + 1),
        g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1))) :=
      Finset.measurable_sum _ fun i _ => (hg_meas _).mul_const _
    -- Parametric integral measurability: pointwise limit of measurable Riemann sums
    have hint_meas : AEStronglyMeasurable (fun ω =>
        ∫ s in Set.Icc 0 t, g s ω ∂volume) μ := by
      -- The Riemann sums are measurable and converge pointwise to the integral
      apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun n ω => ∑ i : Fin (n + 1), g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1)))
      · intro n
        exact (Finset.measurable_sum _ fun i _ => (hg_meas _).mul_const _).aestronglyMeasurable
      · -- From herr_ptwise: err n ω → 0, so Riemann sum → integral
        filter_upwards with ω
        have h := herr_ptwise ω
        have : Filter.Tendsto
            (fun n => err n ω + ∫ s in Set.Icc 0 t, g s ω ∂volume)
            atTop (nhds (0 + ∫ s in Set.Icc 0 t, g s ω ∂volume)) :=
          h.add tendsto_const_nhds
        simp only [err, sub_add_cancel, zero_add] at this
        exact this
    exact (hsum_meas.aestronglyMeasurable.sub hint_meas).pow 2
  -- Step 6: Apply DCT on Ω to get E[error²] → 0
  have hgoal : Filter.Tendsto (fun n => ∫ ω, (err n ω) ^ 2 ∂μ) atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∫ _, (0 : ℝ) ∂μ from by simp]
    exact tendsto_integral_of_dominated_convergence (fun _ => (2 * C * t) ^ 2)
      herr_sq_meas (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact herr_sq_bdd n ω)
      herr_sq_ptwise
  exact hgoal

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

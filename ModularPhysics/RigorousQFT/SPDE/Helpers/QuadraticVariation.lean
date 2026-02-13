/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.StochasticIntegration
import ModularPhysics.RigorousQFT.SPDE.Helpers.ItoFormulaInfrastructure
import ModularPhysics.RigorousQFT.SPDE.Helpers.QuarticBound

/-!
# Quadratic Variation Infrastructure for Itô Processes

This file provides the quadratic variation definition and convergence results
needed for the C² Itô formula proof.

## Main definitions

* `ItoProcess.quadraticVariation` - The quadratic variation [X]_t = ∫₀ᵗ σ(s,ω)² ds.

## Main results

* `ito_process_discrete_qv_L2_convergence` - ∑(ΔXᵢ)² → [X]_t in L².
* `ito_process_qv_sq_integrable` - [X]_t² is integrable when σ is bounded.
* `fatou_squeeze_tendsto_zero` - Fatou squeeze lemma for L¹ convergence to 0.
* `max_partition_increment_ae_zero` - max|ΔXᵢ| → 0 a.s. from path continuity.

## Proof strategy for discrete QV convergence

Decompose ΔXᵢ = drift_i + SI_i where drift_i = ∫_{tᵢ}^{tᵢ₊₁} μ ds and
SI_i = SI(tᵢ₊₁) - SI(tᵢ). Then:
  ∑(ΔXᵢ)² = ∑ drift_i² + 2∑ drift_i·SI_i + ∑ SI_i²

- Term 1: ∑ drift_i² = O(t²/n) → 0 (from |drift_i| ≤ Mμ·Δt)
- Term 2: cross terms → 0 by Cauchy-Schwarz
- Term 3: ∑ SI_i² → ∫₀ᵗ σ² ds via BM QV convergence + weighted QV
-/

open MeasureTheory Filter Finset

namespace SPDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Quadratic variation definition -/

/-- Quadratic variation of an Itô process: [X]_t(ω) = ∫₀ᵗ σ(s,ω)² ds.

    For an Itô process dX_t = μ_t dt + σ_t dW_t, the quadratic variation is
    the total accumulated variance from the diffusion term. The drift does NOT
    contribute to the quadratic variation (its contribution is o(dt)). -/
noncomputable def ItoProcess.quadraticVariation {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in Set.Icc 0 t, (X.diffusion s ω) ^ 2 ∂MeasureTheory.volume

/-- QV is nonneg (integral of nonneg function). -/
theorem ItoProcess.quadraticVariation_nonneg {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ω : Ω) :
    0 ≤ X.quadraticVariation t ω :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s _ => sq_nonneg _)

/-- QV is bounded when diffusion is bounded: [X]_t ≤ Mσ² · t. -/
theorem ItoProcess.quadraticVariation_le {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    X.quadraticVariation t ω ≤ Mσ ^ 2 * t := by
  -- ∫₀ᵗ σ² ds ≤ ∫₀ᵗ Mσ² ds = Mσ²·t (pointwise σ² ≤ Mσ² from |σ| ≤ Mσ)
  sorry

/-- QV squared is integrable when diffusion is bounded.
    Uses: QV ≤ Mσ²t (bounded on probability space → integrable).
    Needs measurability of QV (from measurability of set integral of σ²). -/
theorem ItoProcess.quadraticVariation_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) {Mσ : ℝ} (_hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (_ht : 0 ≤ t) :
    Integrable (fun ω => (X.quadraticVariation t ω) ^ 2) μ := by
  sorry -- Bounded by (Mσ²t)² on probability space; needs AEStronglyMeasurable of QV

/-! ## Discrete QV L² convergence -/

/-- Discrete quadratic variation converges to [X]_t in L².

    ∑ᵢ (X_{tᵢ₊₁} - X_{tᵢ})² → [X]_t = ∫₀ᵗ σ² ds  in L²(μ)

    **Proof strategy**: Decompose ΔXᵢ = drift_i + SI_i and bound each term.
    - drift² terms: O(t/n) in L²
    - cross terms: O(1/√n) in L² by CS + Itô isometry
    - SI² terms: reduce to BM QV via weighted QV convergence

    This is a key ingredient of the C² Itô formula proof. -/
theorem ito_process_discrete_qv_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (_hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (_hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (_ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         X.quadraticVariation t ω) ^ 2 ∂μ)
      atTop (nhds 0) := by
  sorry -- Requires decomposition into drift/SI terms + BM QV convergence

/-! ## Max partition increment -/

/-- For a.e. ω (where path is continuous), every partition increment → 0.

    This uses: continuous function on compact [0,t] is uniformly continuous,
    so |X(t_{i+1},ω) - X(t_i,ω)| → 0 as mesh → 0.

    We prove the pointwise version: for each i, the increment → 0. -/
theorem partition_increment_ae_zero {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ht : 0 < t) :
    ∀ᵐ ω ∂μ, ∀ (i_fn : ∀ n, Fin (n + 1)),
      Filter.Tendsto (fun n =>
        |X.process ((↑(i_fn n : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i_fn n : ℕ) * t / ↑(n + 1)) ω|)
      atTop (nhds 0) := by
  filter_upwards [X.process_continuous] with ω hω_cont
  intro i_fn
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- X(·, ω) is uniformly continuous on compact [0, t]
  have huc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hω_cont.continuousOn.mono
      (fun s hs => hs))
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N, fun n hn => ?_⟩
  set i := i_fn n
  rw [Real.dist_eq, sub_zero]
  -- |ΔXᵢ| = dist(X(tᵢ₊₁,ω), X(tᵢ,ω)) < ε, from uniform continuity + mesh < δ
  have h_dist := hδ
    (↑(i : ℕ) * t / ↑(n + 1)) ?_ ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ?_ ?_
  rw [abs_abs]
  rwa [Real.dist_eq, abs_sub_comm] at h_dist
  -- tᵢ ∈ [0, t]
  · have hi_lt : (i : ℕ) < n + 1 := i.isLt
    constructor
    · positivity
    · have hn1_pos : (0 : ℝ) < ↑(n + 1) := by positivity
      rw [div_le_iff₀ hn1_pos]
      have hi_le : (↑(i : ℕ) : ℝ) ≤ ↑n := by exact_mod_cast Nat.lt_succ_iff.mp hi_lt
      have hn_le : (↑n : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.le_succ n
      linarith [mul_le_mul_of_nonneg_right (hi_le.trans hn_le) (le_of_lt ht)]
  -- tᵢ₊₁ ∈ [0, t]
  · have hi_lt : (i : ℕ) < n + 1 := i.isLt
    constructor
    · positivity
    · have hn1_pos : (0 : ℝ) < ↑(n + 1) := by positivity
      rw [div_le_iff₀ hn1_pos]
      have hi1_le : (↑(i : ℕ) : ℝ) + 1 ≤ ↑(n + 1) := by exact_mod_cast hi_lt
      linarith [mul_le_mul_of_nonneg_right hi1_le (le_of_lt ht)]
  -- dist(tᵢ, tᵢ₊₁) = t/(n+1) < δ
  · rw [Real.dist_eq, show ↑(i : ℕ) * t / ↑(n + 1) - (↑(i : ℕ) + 1) * t / ↑(n + 1) =
      -(t / ↑(n + 1)) from by ring]
    rw [abs_neg, abs_of_nonneg (div_nonneg (le_of_lt ht) (by positivity))]
    have hn1_pos : (0 : ℝ) < ↑(n + 1) := by positivity
    rw [div_lt_iff₀ hn1_pos]
    have hN_le_n : (↑N : ℝ) ≤ ↑n := Nat.cast_le.mpr hn
    have hn_le_n1 : (↑n : ℝ) ≤ ↑(n + 1) := Nat.cast_le.mpr (Nat.le_succ n)
    have h1 : t < ↑N * δ := by
      calc t = (t / δ) * δ := (div_mul_cancel₀ t (ne_of_gt hδ_pos)).symm
        _ < ↑N * δ := by nlinarith
    linarith [mul_le_mul_of_nonneg_right hN_le_n (le_of_lt hδ_pos),
              mul_le_mul_of_nonneg_right hn_le_n1 (le_of_lt hδ_pos)]

/-! ## Fatou squeeze lemma -/

/-- **Fatou squeeze lemma**: If 0 ≤ fₙ ≤ gₙ, fₙ → 0 a.e., gₙ → G a.e.,
    and ∫gₙ → ∫G, then ∫fₙ → 0.

    **Proof**: Apply Fatou's lemma to hₙ := gₙ - fₙ ≥ 0.
    Since hₙ → G a.e.: ∫G = ∫ liminf hₙ ≤ liminf ∫hₙ (Fatou)
                       = liminf(∫gₙ - ∫fₙ) = ∫G - limsup ∫fₙ.
    Hence limsup ∫fₙ ≤ 0. Combined with ∫fₙ ≥ 0: ∫fₙ → 0. -/
theorem fatou_squeeze_tendsto_zero [IsProbabilityMeasure μ]
    {f g : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hf_nn : ∀ n, ∀ ω, 0 ≤ f n ω)
    (hfg : ∀ n, ∀ ω, f n ω ≤ g n ω)
    (hf_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f n ω) atTop (nhds 0))
    (hg_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g n ω) atTop (nhds (G ω)))
    (hf_int : ∀ n, Integrable (f n) μ) (hg_int : ∀ n, Integrable (g n) μ)
    (hG_int : Integrable G μ)
    (hg_tend : Filter.Tendsto (fun n => ∫ ω, g n ω ∂μ)
      atTop (nhds (∫ ω, G ω ∂μ))) :
    Filter.Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (nhds 0) := by
  -- Proof: squeeze between 0 and ∫gₙ - ∫G + ε for large n, using Fatou on gₙ - fₙ.
  -- Equivalently: 0 ≤ ∫fₙ ≤ ∫gₙ - ∫(gₙ - fₙ), and Fatou gives ∫G ≤ liminf ∫(gₙ - fₙ).

  -- Lower bound
  have hf_int_nn : ∀ n, 0 ≤ ∫ ω, f n ω ∂μ :=
    fun n => integral_nonneg (hf_nn n)
  -- Upper bound: ∫fₙ ≤ ∫gₙ
  have hf_le_g : ∀ n, ∫ ω, f n ω ∂μ ≤ ∫ ω, g n ω ∂μ :=
    fun n => integral_mono (hf_int n) (hg_int n) (fun ω => hfg n ω)
  -- Define hₙ = gₙ - fₙ ≥ 0
  set h : ℕ → Ω → ℝ := fun n ω => g n ω - f n ω with hh_def
  -- hₙ → G a.e. (since gₙ → G and fₙ → 0)
  have hh_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => h n ω) atTop (nhds (G ω)) := by
    filter_upwards [hg_ae, hf_ae] with ω hg_ω hf_ω
    have : Filter.Tendsto (fun n => g n ω - f n ω) atTop (nhds (G ω - 0)) :=
      hg_ω.sub hf_ω
    rwa [sub_zero] at this
  -- hₙ ≥ 0
  have hh_nn : ∀ n, ∀ ω, 0 ≤ h n ω :=
    fun n ω => sub_nonneg.mpr (hfg n ω)
  -- hₙ integrable
  have hh_int : ∀ n, Integrable (h n) μ :=
    fun n => (hg_int n).sub (hf_int n)
  -- ∫hₙ = ∫gₙ - ∫fₙ
  have hh_int_eq : ∀ n, ∫ ω, h n ω ∂μ = ∫ ω, g n ω ∂μ - ∫ ω, f n ω ∂μ :=
    fun n => integral_sub (hg_int n) (hf_int n)
  -- Key: ∫fₙ = ∫gₙ - ∫hₙ
  have hf_eq : ∀ n, ∫ ω, f n ω ∂μ = ∫ ω, g n ω ∂μ - ∫ ω, h n ω ∂μ := by
    intro n; linarith [hh_int_eq n]
  -- ∫hₙ ≤ ∫gₙ (since fₙ ≥ 0, so hₙ = gₙ - fₙ ≤ gₙ)
  have hh_le_g_int : ∀ n, ∫ ω, h n ω ∂μ ≤ ∫ ω, g n ω ∂μ :=
    fun n => by linarith [hh_int_eq n, hf_int_nn n]
  -- G ≥ 0 a.e. (limit of nonneg sequence hₙ)
  have hG_nn : 0 ≤ᵐ[μ] G := by
    filter_upwards [hh_ae] with ω hω
    exact ge_of_tendsto' hω (fun n => hh_nn n ω)
  -- Rewrite: ∫fₙ = ∫gₙ - ∫hₙ
  rw [show (fun n => ∫ ω, f n ω ∂μ) = fun n => ∫ ω, g n ω ∂μ - ∫ ω, h n ω ∂μ
    from funext hf_eq,
    show (0 : ℝ) = ∫ ω, G ω ∂μ - ∫ ω, G ω ∂μ from (sub_self _).symm]
  apply Filter.Tendsto.sub hg_tend
  -- Goal: Tendsto (fun n => ∫ ω, h n ω ∂μ) atTop (nhds (∫ ω, G ω ∂μ))
  -- Prove via ENNReal: Fatou gives lower bound, monotonicity gives upper bound.
  -- Step A: Fatou in ENNReal — ofReal(∫G) ≤ liminf ofReal(∫hₙ)
  have h_fatou : ENNReal.ofReal (∫ ω, G ω ∂μ) ≤
      Filter.liminf (fun n => ENNReal.ofReal (∫ ω, h n ω ∂μ)) atTop := by
    rw [ofReal_integral_eq_lintegral_ofReal hG_int hG_nn]
    simp_rw [fun n => ofReal_integral_eq_lintegral_ofReal (hh_int n) (ae_of_all _ (hh_nn n))]
    have h_liminf_ae : ∀ᵐ ω ∂μ, Filter.liminf (fun n => ENNReal.ofReal (h n ω)) atTop =
        ENNReal.ofReal (G ω) := by
      filter_upwards [hh_ae] with ω hω
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq
    calc ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ
        = ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal (h n ω)) atTop ∂μ :=
          lintegral_congr_ae (h_liminf_ae.mono fun ω hω => hω.symm)
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ) atTop :=
          lintegral_liminf_le' fun n =>
            ENNReal.continuous_ofReal.measurable.comp_aemeasurable
              (hh_int n).aestronglyMeasurable.aemeasurable
  -- Step B: limsup ofReal(∫hₙ) ≤ ofReal(∫G)
  have h_limsup : Filter.limsup (fun n => ENNReal.ofReal (∫ ω, h n ω ∂μ)) atTop ≤
      ENNReal.ofReal (∫ ω, G ω ∂μ) :=
    calc Filter.limsup (fun n => ENNReal.ofReal (∫ ω, h n ω ∂μ)) atTop
        ≤ Filter.limsup (fun n => ENNReal.ofReal (∫ ω, g n ω ∂μ)) atTop :=
          Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n =>
            ENNReal.ofReal_le_ofReal (hh_le_g_int n))
      _ = ENNReal.ofReal (∫ ω, G ω ∂μ) :=
          ((ENNReal.continuous_ofReal.tendsto _).comp hg_tend).limsup_eq
  -- Step C: ofReal(∫hₙ) → ofReal(∫G) in ENNReal (liminf/limsup squeeze)
  have h_ennreal_tend := tendsto_of_le_liminf_of_limsup_le h_fatou h_limsup
  -- Step D: Convert back to ℝ via toReal
  have h_toReal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h_ennreal_tend
  simp only [Function.comp_def] at h_toReal
  rwa [show (fun n => (ENNReal.ofReal (∫ ω, h n ω ∂μ)).toReal) =
      fun n => ∫ ω, h n ω ∂μ from
      funext fun n => ENNReal.toReal_ofReal (integral_nonneg (hh_nn n)),
    show (ENNReal.ofReal (∫ ω, G ω ∂μ)).toReal = ∫ ω, G ω ∂μ from
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hG_nn)] at h_toReal

/-! ## Taylor remainder a.e. convergence -/

/-- Along an a.e.-convergent subsequence for QV, the Taylor remainders
    converge to 0 a.e.

    **Key argument**: For a.e. ω where path is continuous:
    - max|ΔXᵢ(ω)| → 0 (from uniform continuity on compact interval)
    - f''_t is uniformly continuous on the compact range of X(·,ω)
    - By integral form of C² Taylor remainder:
      |Rᵢ| ≤ ω_{f''}(|ΔXᵢ|) · (ΔXᵢ)²/2
    - Hence |∑ Rᵢ| ≤ ω_{f''}(max|ΔXⱼ|)/2 · ∑(ΔXᵢ)²
    - Since ∑(ΔXᵢ)² → [X]_t and ω_{f''}(max|ΔXⱼ|) → 0:
      (∑ Rᵢ)² → 0 · [X]_t² = 0 a.s. -/
theorem taylor_remainders_ae_tendsto_zero {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mf'' : ℝ} (_hMf'' : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf'')
    (t : ℝ) (_ht : 0 < t)
    (ns : ℕ → ℕ) (_hns : StrictMono ns)
    (_h_qv_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
      ∑ i : Fin (ns k + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) ^ 2)
      atTop (nhds (X.quadraticVariation t ω))) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
      (∑ i : Fin (ns k + 1),
        (f (↑(i : ℕ) * t / ↑(ns k + 1))
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(ns k + 1))
           (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(ns k + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) -
         (1 : ℝ) / 2 *
           deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(ns k + 1)) x))
             (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) ^ 2)) ^ 2)
      atTop (nhds 0) := by
  sorry -- Integral form of C² Taylor remainder + modulus of continuity of f''

end SPDE

/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.StochasticIntegration
import ModularPhysics.RigorousQFT.SPDE.Helpers.ItoFormulaInfrastructure
import ModularPhysics.RigorousQFT.SPDE.Helpers.ItoFormulaDecomposition
import ModularPhysics.RigorousQFT.SPDE.Helpers.ItoIntegralProperties
import Mathlib.Analysis.Calculus.Taylor

/-!
# Itô Formula Proof Infrastructure

This file provides the proof of the Itô formula martingale property (part ii).

## Strategy

The key theorem `ito_formula_martingale` shows that the stochastic integral remainder
M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [generalized drift] ds is a martingale.

**Proof approach**: Show M_t is an L² limit of simple stochastic integrals,
then apply `ito_integral_martingale_setIntegral`.

For partition 0 = t₀ < t₁ < ... < tₙ = T, construct simple process:
  H_n(s) = ∂_x f(tᵢ, X_{tᵢ}) · σ_{tᵢ}  on [tᵢ, tᵢ₊₁)

Then: stoch_int(T) - ∫ H_n dW_T = error terms → 0 in L².

Error decomposition:
- Taylor remainder: controlled by ‖f''‖_∞ · |ΔX|³
- Weighted QV: Σ f''·σ² · [(ΔW)² - Δt] → 0 (weighted_qv_L2_convergence)
- Riemann sum error: Σ g(tᵢ)Δt - ∫ g ds → 0
- Cross terms: (Δt)·(ΔW) terms are O(Δt^{3/2})

## Main results

- `itoPartitionProcess`: construction of approximating simple process
- `ito_formula_L2_convergence`: the L² convergence estimate
- `ito_formula_martingale`: the martingale property
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Taylor expansion bound for C² functions

Second-order Taylor: f(x) = f(a) + f'(a)(x-a) + ½f''(ξ)(x-a)² for some ξ.
We use the Lagrange form remainder bound from Mathlib. -/

/-- Second-order Taylor bound: for C² function f on [a, b],
    |f(b) - f(a) - f'(a)(b-a)| ≤ M · (b-a)² where M bounds |f''|.

    This is `taylor_mean_remainder_bound` from Mathlib with n=1. -/
theorem taylor_second_order_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b)) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDerivWithin 2 f (Set.Icc a b) y‖ ≤ M) :
    ‖f b - taylorWithinEval f 1 (Set.Icc a b) a b‖ ≤ M * (b - a) ^ 2 := by
  have h := taylor_mean_remainder_bound hab hf (Set.right_mem_Icc.mpr hab) hM
  simp only [show (1 : ℕ) + 1 = 2 from rfl, Nat.factorial_one, Nat.cast_one, div_one] at h
  exact h

/-- The 1st-order Taylor polynomial of f at a evaluated at b equals f(a) + f'(a)(b-a). -/
theorem taylorWithinEval_one {f : ℝ → ℝ} {a b : ℝ} {s : Set ℝ} :
    taylorWithinEval f 1 s a b = f a + derivWithin f s a * (b - a) := by
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ]
  ring

/-- Derivative of a C² function is continuous. -/
theorem contDiff_two_deriv_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (deriv f) :=
  ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.continuous

/-! ## Construction of partition simple process -/

/-- For a partition of [0, T] into n equal parts, the partition time for index i. -/
def partitionTime (T : ℝ) (n : ℕ) (i : ℕ) : ℝ := ↑i * T / ↑n

/-- Partition times are nonneg when T ≥ 0. -/
theorem partitionTime_nonneg {T : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n) (i : ℕ) :
    0 ≤ partitionTime T n i := by
  unfold partitionTime; positivity

/-- Partition times are monotone when T ≥ 0. -/
theorem partitionTime_mono {T : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n) {i j : ℕ} (hij : i ≤ j) :
    partitionTime T n i ≤ partitionTime T n j := by
  unfold partitionTime
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hn).le
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT

/-- Partition times are strictly monotone when T > 0. -/
theorem partitionTime_strictMono {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n)
    {i j : ℕ} (hij : i < j) :
    partitionTime T n i < partitionTime T n j := by
  unfold partitionTime
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hn)
  exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) hT

/-- Partition time at n equals T. -/
theorem partitionTime_n {T : ℝ} {n : ℕ} (hn : 0 < n) :
    partitionTime T n n = T := by
  unfold partitionTime; field_simp

/-- The time step T/n. -/
theorem partitionTime_step {T : ℝ} {n : ℕ} (_hn : 0 < n) (i : ℕ) :
    partitionTime T n (i + 1) - partitionTime T n i = T / ↑n := by
  unfold partitionTime
  rw [Nat.cast_succ, add_mul, one_mul, add_div, add_sub_cancel_left]

/-- Construct the approximating simple process for the Itô formula.

    For a uniform partition of [0, T] with n intervals, the simple process
    has values ∂_x f(tᵢ, X_{tᵢ}) · σ_{tᵢ} on [tᵢ, tᵢ₊₁).

    We need n+1 partition points for n intervals. -/
def itoPartitionProcess {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) : SimpleProcess F where
  n := n + 1
  times i := partitionTime T n (i : ℕ)
  values i ω :=
    deriv (fun x => f (partitionTime T n (i : ℕ)) x) (X.process (partitionTime T n (i : ℕ)) ω) *
    X.diffusion (partitionTime T n (i : ℕ)) ω
  increasing := by
    intro i j hij
    exact partitionTime_strictMono hT hn (by exact hij)
  adapted := by
    intro i
    have hderiv_cont : Continuous (deriv (fun x => f (partitionTime T n (i : ℕ)) x)) :=
      contDiff_two_deriv_continuous (hf_x _)
    have hX_meas : Measurable (X.process (partitionTime T n (i : ℕ))) :=
      (X.process_adapted _).mono (F.le_ambient _) le_rfl
    exact (hderiv_cont.measurable.comp hX_meas).mul (hdiff_meas _)

/-! ## Adapted properties of the partition process

These lemmas verify that the partition simple process satisfies the hypotheses
needed for `ito_integral_martingale_setIntegral`. -/

/-- The partition process values are BM.F-adapted.
    This is the adaptedness condition needed for the martingale theorem. -/
theorem itoPartitionProcess_adapted {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ) (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t)) :
    ∀ i : Fin (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra
        ((itoPartitionProcess X f hf_x hdiff_meas T hT n hn).times i)) _
        ((itoPartitionProcess X f hf_x hdiff_meas T hT n hn).values i) := by
  intro i
  show @Measurable Ω ℝ (X.BM.F.σ_algebra (partitionTime T n (i : ℕ))) _
    (fun ω => deriv (fun x => f (partitionTime T n (i : ℕ)) x)
      (X.process (partitionTime T n (i : ℕ)) ω) *
      X.diffusion (partitionTime T n (i : ℕ)) ω)
  have hderiv_cont : Continuous (deriv (fun x => f (partitionTime T n (i : ℕ)) x)) :=
    contDiff_two_deriv_continuous (hf_x _)
  -- X.process is F-adapted, and F ≤ BM.F
  have hX_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (partitionTime T n (i : ℕ))) _
      (X.process (partitionTime T n (i : ℕ))) :=
    (X.process_adapted _).mono (X.F_le_BM_F _) le_rfl
  have hdiff_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (partitionTime T n (i : ℕ))) _
      (X.diffusion (partitionTime T n (i : ℕ))) :=
    (hdiff_adapted _).mono (X.F_le_BM_F _) le_rfl
  exact (hderiv_cont.measurable.comp hX_BM).mul hdiff_BM

/-- The partition process values are bounded when f' and σ are bounded. -/
theorem itoPartitionProcess_bounded {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M) :
    ∀ i : Fin (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).n,
      ∃ C : ℝ, ∀ ω, |(itoPartitionProcess X f hf_x hdiff_meas T hT n hn).values i ω| ≤ C := by
  intro i
  obtain ⟨M₁, hM₁⟩ := hf_x_bdd
  obtain ⟨M₂, hM₂⟩ := hdiff_bdd
  refine ⟨|M₁| * |M₂|, fun ω => ?_⟩
  show |deriv (fun x => f _ x) _ * X.diffusion _ ω| ≤ _
  rw [abs_mul]
  exact mul_le_mul
    (le_trans (hM₁ _ _) (le_abs_self M₁))
    (le_trans (hM₂ _ _) (le_abs_self M₂))
    (abs_nonneg _) (abs_nonneg _)

/-- The partition process times are nonneg. -/
theorem itoPartitionProcess_times_nonneg {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) :
    ∀ i : Fin (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).n,
      0 ≤ (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).times i := by
  intro i
  show 0 ≤ partitionTime T n _
  exact partitionTime_nonneg hT.le hn _

/-! ## Itô formula remainder definition -/

/-- The Itô formula remainder (stochastic integral part):
    M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds

    This is the process that the Itô formula asserts is a martingale. -/
def itoRemainder {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  f t (X.process t ω) - f 0 (X.process 0 ω) -
  ∫ s in Set.Icc 0 t,
    (deriv (fun u => f u (X.process s ω)) s +
     deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
     (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2) ∂volume

/-! ## Second derivative continuity -/

/-- The second derivative of a C² function is continuous. -/
theorem contDiff_two_snd_deriv_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (deriv (deriv f)) :=
  ((contDiff_succ_iff_deriv (n := 0)).mp
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).2.2.continuous

/-! ## Weighted QV convergence for Itô formula

The key analytical estimate: the weighted quadratic variation term
  Σᵢ ½f''(tᵢ, Xᵢ) · σ²ᵢ · [(ΔWᵢ)² - Δtᵢ]
converges to 0 in L² as the partition mesh → 0.

This is the mathematical core of the Itô formula proof, using
`weighted_qv_L2_convergence` from ItoFormulaInfrastructure.lean. -/

/-- The QV weights ½f''(tᵢ, Xᵢ)σ²ᵢ are BM.F-adapted at partition times.
    This is needed to apply `weighted_qv_L2_convergence`. -/
theorem ito_qv_weights_adapted {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (t : ℝ) (n : ℕ) :
    ∀ i : Fin (n + 1),
    @Measurable Ω ℝ (X.BM.F.σ_algebra (↑(i : ℕ) * t / ↑(n + 1))) _
      (fun ω => (1 : ℝ) / 2 *
        deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
        (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) := by
  intro i
  -- f'' is continuous (from C² regularity)
  have hf''_cont : Continuous (deriv (deriv (fun x =>
      f (↑(i : ℕ) * t / ↑(n + 1)) x))) :=
    contDiff_two_snd_deriv_continuous (hf_x _)
  -- X.process is BM.F-adapted (from process_adapted + F_le_BM_F)
  have hX_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (↑(i : ℕ) * t / ↑(n + 1))) _
      (X.process (↑(i : ℕ) * t / ↑(n + 1))) :=
    (X.process_adapted _).mono (X.F_le_BM_F _) le_rfl
  -- σ is BM.F-adapted
  have hσ_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (↑(i : ℕ) * t / ↑(n + 1))) _
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1))) :=
    (hdiff_adapted _).mono (X.F_le_BM_F _) le_rfl
  -- f''(X(·)) is BM.F-measurable (composition of continuous and measurable)
  have hf''_comp := hf''_cont.measurable.comp hX_BM
  -- Full weight: (1/2 * f''(X)) * σ² is BM.F-measurable
  -- Uses: const is measurable, f''∘X is measurable, σ² is measurable
  apply Measurable.mul
  · exact Measurable.mul measurable_const hf''_comp
  · exact hσ_BM.pow_const 2

/-- The QV weights ½f''(tᵢ, Xᵢ)σ²ᵢ are uniformly bounded.
    Bound: |g| ≤ ½ · |Mf| · Mσ² where Mf bounds |f''| and Mσ bounds |σ|. -/
theorem ito_qv_weights_bounded {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    {Mf : ℝ} (hMf : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (n : ℕ) :
    ∀ i : Fin (n + 1), ∀ ω,
    |(1 : ℝ) / 2 *
      deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| ≤
    1 / 2 * |Mf| * Mσ ^ 2 := by
  intro i ω
  have h1 : |deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
      (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω)| ≤ |Mf| :=
    le_trans (hMf _ _) (le_abs_self _)
  have h2 : |(X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| ≤ Mσ ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hMσ _ ω)).1 (abs_le.mp (hMσ _ ω)).2
  calc |(1 : ℝ) / 2 *
      deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2|
      = |(1 : ℝ) / 2| *
        |deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω)| *
        |(X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 / 2 * |Mf| * Mσ ^ 2 := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
          (abs_nonneg _) (by positivity)

/-- The weighted QV term in the Itô formula converges to 0 in L².

    For partition 0 = t₀ < t₁ < ... < tₙ = t with uniform mesh t/n:
    E[(Σᵢ ½f''(tᵢ, X_{tᵢ}) · σ²_{tᵢ} · ((ΔWᵢ)² - Δtᵢ))²] → 0.

    This is the primary analytical content of the Itô formula. -/
theorem ito_weighted_qv_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          ((1 : ℝ) / 2 *
            deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
              (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
            (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) *
          ((X.BM.toAdapted.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
            X.BM.toAdapted.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
           t / ↑(n + 1)))^2 ∂μ)
      atTop (nhds 0) := by
  -- Extract explicit bounds from hypotheses
  obtain ⟨Mf, hMf⟩ := hf_xx_bdd
  obtain ⟨Mσ, hMσ⟩ := hdiff_bdd
  -- Apply weighted_qv_L2_convergence with bound C = ½|Mf|Mσ²
  exact weighted_qv_L2_convergence X.BM t ht (1 / 2 * |Mf| * Mσ ^ 2) (by positivity)
    (fun n i => fun ω => (1 : ℝ) / 2 *
      deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2)
    (fun n => ito_qv_weights_adapted X f hf_x hdiff_adapted t n)
    (fun n i ω => ito_qv_weights_bounded X f hMf hMσ t n i ω)

/-! ## L² convergence of partition sums

The main estimate showing that the simple stochastic integrals converge
to the Itô formula remainder in L².

**Proof structure:**
The error S_n(t) - M_t decomposes as:
  S_n - M = -(weighted QV) + (lower order)
where:
- weighted QV = Σ ½f''σ²[(ΔW)²-Δt] → 0 (by `ito_weighted_qv_convergence`)
- lower order = Taylor remainders + Riemann sum errors + cross terms → 0

By (a+b)² ≤ 2a² + 2b², the total L² error is bounded by
  2·E[|QV|²] + 2·E[|lower|²] → 0. -/

/-- Lower-order error terms in the Itô formula converge to 0 in L².
    These include:
    1. Space Taylor remainders: O(|ΔX|³) per interval
    2. Time Taylor remainders: O(Δt · |ΔX|) per interval
    3. Riemann sum errors: Σ g(tᵢ)Δt vs ∫ g ds
    4. Cross terms: Σ f'(ΔSI - σΔW), (ΔX)²-(ΔSI)², etc.

    Each is o(1) in L² as mesh → 0, using boundedness of drift/diffusion. -/
theorem ito_lower_order_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (SimpleProcess.stochasticIntegral_at
          (itoPartitionProcess X f hf_x hdiff_meas t ht (n + 1) (Nat.succ_pos n)) X.BM t ω -
         itoRemainder X f t ω +
         -- The QV term (which we add back since it was subtracted in the decomposition)
         ∑ i : Fin (n + 1),
          ((1 : ℝ) / 2 *
            deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
              (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
            (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) *
          ((X.BM.toAdapted.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
            X.BM.toAdapted.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
           t / ↑(n + 1)))^2 ∂μ)
      atTop (nhds 0) := by
  sorry

/-- The key L² convergence estimate for the Itô formula.

    For the uniform partition with n intervals on [0, t]:
    E[|itoRemainder(t) - ∫ H_n dW_t|²] → 0 as n → ∞

    The error decomposes as:
    1. Weighted QV: Σ f''σ²[(ΔW)²-Δt] → 0 (PROVED via `ito_weighted_qv_convergence`)
    2. Lower order: Taylor remainders + Riemann sums + cross terms → 0 -/
theorem ito_formula_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    -- Regularity of diffusion
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    -- Regularity of drift
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    -- Boundedness of derivatives
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    -- Integrability of the Itô remainder (provided by caller, follows from regularity)
    (hrem_sq_int : Integrable (fun ω => (itoRemainder X f t ω)^2) μ)
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (SimpleProcess.stochasticIntegral_at
          (itoPartitionProcess X f hf_x hdiff_meas t ht (n + 1) (Nat.succ_pos n)) X.BM t ω -
         itoRemainder X f t ω)^2 ∂μ)
      atTop (nhds 0) := by
  -- Define the weighted QV and lower-order terms
  let qv : ℕ → Ω → ℝ := fun n ω =>
    ∑ i : Fin (n + 1),
      ((1 : ℝ) / 2 *
        deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
        (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) *
      ((X.BM.toAdapted.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
        X.BM.toAdapted.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       t / ↑(n + 1))
  let error : ℕ → Ω → ℝ := fun n ω =>
    SimpleProcess.stochasticIntegral_at
      (itoPartitionProcess X f hf_x hdiff_meas t ht (n + 1) (Nat.succ_pos n)) X.BM t ω -
    itoRemainder X f t ω
  -- lower = error + qv (the QV-free remainder)
  let lower : ℕ → Ω → ℝ := fun n ω => error n ω + qv n ω
  -- Tautological decomposition: error = -qv + lower
  have hdecomp : ∀ n ω, error n ω = -qv n ω + lower n ω := by
    intro n ω; show _ = -(qv n ω) + (error n ω + qv n ω); ring
  -- Step 1: E[|qv|²] → 0 by weighted_qv_L2_convergence
  have hqv_conv : Filter.Tendsto (fun n => ∫ ω, (qv n ω)^2 ∂μ) atTop (nhds 0) :=
    ito_weighted_qv_convergence X f hf_x hdiff_adapted hdiff_bdd hf_xx_bdd t ht.le
  -- Step 2: E[|lower|²] → 0 (lower-order terms)
  have hlower_conv : Filter.Tendsto (fun n => ∫ ω, (lower n ω)^2 ∂μ) atTop (nhds 0) :=
    ito_lower_order_L2_convergence X f hf_t hf_x hdiff_meas hdiff_adapted
      hdiff_bdd hdrift_bdd hf_x_bdd hf_xx_bdd t ht
  -- Step 3: Combine via (a+b)² ≤ 2a² + 2b²
  apply squeeze_zero
  · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
  · intro n
    -- Rewrite error using decomposition
    have hrewrite : (fun ω => (error n ω) ^ 2) =
        fun ω => (-qv n ω + lower n ω) ^ 2 := by
      ext ω; rw [hdecomp]
    -- (-a + b)² ≤ 2a² + 2b²
    calc ∫ ω, (error n ω) ^ 2 ∂μ
        = ∫ ω, (-qv n ω + lower n ω) ^ 2 ∂μ := by rw [hrewrite]
      _ ≤ ∫ ω, (2 * (qv n ω) ^ 2 + 2 * (lower n ω) ^ 2) ∂μ := by
          apply integral_mono_ae
          · sorry -- integrability of error² (from boundedness of terms)
          · sorry -- integrability of 2·qv² + 2·lower² (from boundedness)
          · exact ae_of_all _ fun ω => by nlinarith [sq_nonneg (qv n ω + lower n ω)]
      _ ≤ 2 * ∫ ω, (qv n ω) ^ 2 ∂μ + 2 * ∫ ω, (lower n ω) ^ 2 ∂μ := by
          sorry -- integral_add + integral_const_mul (needs integrability)
  · -- 2·E[qv²] + 2·E[lower²] → 0
    rw [show (0 : ℝ) = 2 * 0 + 2 * 0 from by ring]
    exact (hqv_conv.const_mul 2).add (hlower_conv.const_mul 2)

/-! ## Main martingale property theorem

Applies `ito_integral_martingale_setIntegral` using the L² convergence. -/

/-- The Itô formula remainder is a martingale.

    This is the key content of the Itô formula: the process
    M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds
    satisfies the martingale set-integral property. -/
theorem ito_formula_martingale {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    -- Regularity of diffusion
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    -- Regularity of drift
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    -- Boundedness of derivatives
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    -- Integrability of the remainder (verified by caller using boundedness of f, drift, etc.)
    (hrem_int : ∀ t', 0 ≤ t' → Integrable (itoRemainder X f t') μ)
    (hrem_sq_int : ∀ t', 0 ≤ t' → Integrable (fun ω => (itoRemainder X f t' ω)^2) μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, itoRemainder X f t ω ∂μ = ∫ ω in A, itoRemainder X f s ω ∂μ := by
  intro s t hs hst A hA
  -- Handle the trivial case s = t
  by_cases hst_eq : s = t
  · subst hst_eq; rfl
  -- For s < t, apply ito_integral_martingale_setIntegral
  have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
  have ht_pos : 0 < t := lt_of_le_of_lt hs hst_lt
  -- Transfer measurability from F to BM.F
  have hA_BM : MeasurableSet[X.BM.F.σ_algebra s] A :=
    (X.F_le_BM_F s) _ hA
  -- Apply ito_integral_martingale_setIntegral
  exact SPDE.ito_integral_martingale_setIntegral X.BM (itoRemainder X f)
    (fun n => itoPartitionProcess X f hf_x hdiff_meas t ht_pos (n + 1) (Nat.succ_pos n))
    (fun n => itoPartitionProcess_adapted X f hf_x hdiff_meas t ht_pos
      (n + 1) (Nat.succ_pos n) hdiff_adapted)
    (fun n => itoPartitionProcess_bounded X f hf_x hdiff_meas t ht_pos
      (n + 1) (Nat.succ_pos n) hf_x_bdd hdiff_bdd)
    (fun n => itoPartitionProcess_times_nonneg X f hf_x hdiff_meas t ht_pos
      (n + 1) (Nat.succ_pos n))
    (fun t' ht'_nn ht'_le => by
      -- L² convergence: this is `ito_formula_L2_convergence` restricted to [0, t]
      sorry)
    (fun t' ht'_nn ht'_le => hrem_int t' ht'_nn)
    (fun t' ht'_nn ht'_le => hrem_sq_int t' ht'_nn)
    hs hst le_rfl hA_BM

end SPDE

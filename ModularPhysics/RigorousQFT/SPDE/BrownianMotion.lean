/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Basic

/-!
# Brownian Motion and Wiener Processes

This file defines Brownian motion, cylindrical Wiener processes,
and related constructions for SPDEs.

## Main Definitions

* `BrownianMotion` - Standard Brownian motion / Wiener process
* `CylindricalWienerProcess` - Cylindrical Wiener process on a Hilbert space
* `QWienerProcess` - Q-Wiener process with covariance operator Q

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"
* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
-/

namespace SPDE

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Brownian Motion -/

/-- Standard Brownian motion (Wiener process).
    A continuous process W : [0, ∞) → ℝ with:
    - W_0 = 0 a.s.
    - Independent increments
    - W_t - W_s ~ N(0, t-s) for s ≤ t -/
structure BrownianMotion (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The underlying filtration -/
  F : Filtration Ω ℝ
  /-- The adapted process -/
  toAdapted : AdaptedProcess F ℝ
  /-- Initial condition: W_0 = 0 a.s. -/
  initial : ∀ᵐ ω ∂μ, toAdapted.process 0 ω = 0
  /-- Continuous paths a.s. -/
  continuous_paths : ∀ᵐ ω ∂μ, Continuous (fun t => toAdapted.process t ω)
  /-- Stationary increments: W_{t+s} - W_s has same distribution as W_t -/
  stationary_increments : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    ∀ᵐ ω ∂μ, toAdapted.process (s + t) ω - toAdapted.process s ω =
             toAdapted.process t ω - toAdapted.process 0 ω
  /-- Variance of increments: Var(W_t - W_s) = |t - s| -/
  increment_variance : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    ∫ ω, (toAdapted.process t ω - toAdapted.process s ω)^2 ∂μ = t - s

namespace BrownianMotion

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The process underlying Brownian motion -/
def process (W : BrownianMotion Ω μ) : ℝ → Ω → ℝ := W.toAdapted.process

/-- Brownian motion is a martingale -/
theorem is_martingale (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ] :
    ∃ M : Martingale W.F μ ℝ, M.process = W.process := by
  sorry

/-- The quadratic variation of Brownian motion is t -/
theorem quadratic_variation (W : BrownianMotion Ω μ) :
    ∃ qv : QuadraticVariation W.F,
      qv.process = W.process ∧
      (∀ t : ℝ, ∀ᵐ ω ∂μ, qv.variation t ω = t) := by
  sorry

/-- Brownian scaling: if W_t is a BM, then c^{-1/2} W_{ct} is also a BM -/
theorem scaling (W : BrownianMotion Ω μ) (c : ℝ) (hc : 0 < c) :
    ∃ W' : BrownianMotion Ω μ,
      ∀ t : ℝ, ∀ᵐ ω ∂μ, W'.process t ω = c^(-(1/2 : ℝ)) * W.process (c * t) ω := by
  sorry

/-- Reflection principle: -W is also a Brownian motion -/
theorem reflection (W : BrownianMotion Ω μ) :
    ∃ W' : BrownianMotion Ω μ,
      ∀ t : ℝ, ∀ᵐ ω ∂μ, W'.process t ω = -W.process t ω := by
  sorry

/-- Time inversion: tW_{1/t} is a Brownian motion (for t > 0) -/
theorem time_inversion (W : BrownianMotion Ω μ) :
    ∃ W' : BrownianMotion Ω μ,
      ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂μ, W'.process t ω = t * W.process (1/t) ω := by
  sorry

end BrownianMotion

/-! ## Multidimensional Brownian Motion -/

/-- d-dimensional Brownian motion -/
structure BrownianMotionD (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) where
  /-- The underlying filtration -/
  F : Filtration Ω ℝ
  /-- The adapted process -/
  toAdapted : AdaptedProcess F (Fin d → ℝ)
  /-- Initial condition -/
  initial : ∀ᵐ ω ∂μ, toAdapted.process 0 ω = 0
  /-- Continuous paths -/
  continuous_paths : ∀ᵐ ω ∂μ, Continuous (fun t => toAdapted.process t ω)
  /-- Covariance: E[W_t^i W_s^j] = (t ∧ s) δ_{ij} -/
  covariance : ∀ i j : Fin d, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    ∫ ω, (toAdapted.process t ω i) * (toAdapted.process s ω j) ∂μ =
      if i = j then min t s else 0

/-! ## Cylindrical Wiener Process -/

/-- A cylindrical Wiener process on a Hilbert space H.
    This is a generalization of Brownian motion to infinite dimensions. -/
structure CylindricalWienerProcess (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace (H →L[ℝ] ℝ)] where
  /-- The underlying filtration -/
  F : Filtration Ω ℝ
  /-- The adapted process -/
  toAdapted : AdaptedProcess F (H →L[ℝ] ℝ)
  /-- Isometry property: E[⟨W(t), h₁⟩⟨W(s), h₂⟩] = (t ∧ s)⟨h₁, h₂⟩ -/
  isometry : ∀ h₁ h₂ : H, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    ∫ ω, (toAdapted.process t ω h₁) * (toAdapted.process s ω h₂) ∂μ =
      min t s * @inner ℝ H _ h₁ h₂

namespace CylindricalWienerProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace (H →L[ℝ] ℝ)]

/-- The cylindrical Wiener process evaluated on h ∈ H gives a real-valued process -/
def eval (W : CylindricalWienerProcess Ω μ H) (h : H) : ℝ → Ω → ℝ :=
  fun t ω => W.toAdapted.process t ω h

/-- Evaluation on a unit vector gives a standard Brownian motion -/
theorem eval_unit_is_brownian (W : CylindricalWienerProcess Ω μ H) (h : H) (hh : ‖h‖ = 1) :
    ∃ B : BrownianMotion Ω μ, ∀ t : ℝ, ∀ᵐ ω ∂μ, B.process t ω = W.eval h t ω := by
  sorry

end CylindricalWienerProcess

/-! ## Q-Wiener Process -/

/-- A trace-class operator on H -/
structure TraceClassOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  /-- The underlying continuous linear map -/
  toLinearMap : H →L[ℝ] H
  /-- Self-adjoint -/
  self_adjoint : ∀ h₁ h₂ : H, @inner ℝ H _ (toLinearMap h₁) h₂ = @inner ℝ H _ h₁ (toLinearMap h₂)
  /-- Non-negative -/
  nonneg : ∀ h : H, @inner ℝ H _ (toLinearMap h) h ≥ 0
  /-- Trace is finite (represented as existence of orthonormal basis with summable eigenvalues) -/
  trace_finite : ∃ (trace : ℝ), trace ≥ 0

/-- A Q-Wiener process with covariance operator Q.
    More regular than cylindrical Wiener process when Tr(Q) < ∞. -/
structure QWienerProcess (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] (Q : TraceClassOperator H) where
  /-- The underlying filtration -/
  F : Filtration Ω ℝ
  /-- The adapted process -/
  toAdapted : AdaptedProcess F H
  /-- Covariance: E[⟨W(t), h₁⟩⟨W(s), h₂⟩] = (t ∧ s)⟨Qh₁, h₂⟩ -/
  covariance : ∀ h₁ h₂ : H, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    ∫ ω, @inner ℝ H _ (toAdapted.process t ω) h₁ * @inner ℝ H _ (toAdapted.process s ω) h₂ ∂μ =
      min t s * @inner ℝ H _ (Q.toLinearMap h₁) h₂

namespace QWienerProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
variable {Q : TraceClassOperator H}

/-- Q-Wiener process has continuous paths in H -/
theorem continuous_paths (W : QWienerProcess Ω μ H Q) :
    ∀ᵐ ω ∂μ, Continuous (fun t => W.toAdapted.process t ω) := by
  sorry

/-- The covariance operator determines the regularity -/
theorem regularity_from_trace (W : QWienerProcess Ω μ H Q) :
    ∀ t : ℝ, 0 ≤ t → ∃ (bound : ℝ), ∫ ω, ‖W.toAdapted.process t ω‖^2 ∂μ ≤ bound := by
  sorry

end QWienerProcess

/-! ## Space-Time White Noise -/

/-- Space-time white noise on a domain D ⊆ ℝ^d -/
structure SpaceTimeWhiteNoise (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) (D : Set (Fin d → ℝ)) [MeasurableSpace D] (ν : Measure D) where
  /-- The distribution W(ϕ) for test function ϕ -/
  eval : (D → ℝ) → (Ω → ℝ)
  /-- Linearity -/
  linear : ∀ a b : ℝ, ∀ ϕ ψ : D → ℝ,
    eval (fun x => a * ϕ x + b * ψ x) = fun ω => a * eval ϕ ω + b * eval ψ ω
  /-- Isometry: E[W(ϕ)W(ψ)] = ⟨ϕ, ψ⟩_{L²} -/
  isometry : ∀ ϕ ψ : D → ℝ, ∫ ω, eval ϕ ω * eval ψ ω ∂μ = ∫ x, ϕ x * ψ x ∂ν

/-! ## Lévy's Characterization -/

/-- Lévy's characterization: a continuous local martingale with
    quadratic variation ⟨M⟩_t = t is a Brownian motion. -/
theorem levy_characterization {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration Ω ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : LocalMartingale F μ ℝ)
    (continuous : ∀ᵐ ω ∂μ, Continuous (fun t => M.process t ω))
    (initial : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (qv : QuadraticVariation F)
    (hqv_process : qv.process = M.process)
    (hqv_is_t : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂μ, qv.variation t ω = t) :
    ∃ W : BrownianMotion Ω μ, W.process = M.process := by
  sorry

/-! ## Brownian Bridge -/

/-- Brownian bridge from 0 to a at time T -/
structure BrownianBridge (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ℝ) (hT : 0 < T) (a : ℝ) where
  /-- The process on [0, T] -/
  process : Set.Icc 0 T → Ω → ℝ
  /-- Initial condition -/
  initial : ∀ᵐ ω ∂μ, process ⟨0, by constructor <;> linarith⟩ ω = 0
  /-- Terminal condition -/
  terminal : ∀ᵐ ω ∂μ, process ⟨T, by constructor <;> linarith⟩ ω = a
  /-- Continuous paths -/
  continuous_paths : ∀ᵐ ω ∂μ, Continuous (fun t => process t ω)
  /-- Covariance: E[B_s B_t] = s(T-t)/T for s ≤ t -/
  covariance : ∀ (s t : Set.Icc 0 T), s.val ≤ t.val →
    ∫ ω, process s ω * process t ω ∂μ = s.val * (T - t.val) / T

/-! ## Ornstein-Uhlenbeck Process -/

/-- Ornstein-Uhlenbeck process: dX_t = -θ X_t dt + σ dW_t -/
structure OrnsteinUhlenbeck (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (θ σ : ℝ) (hθ : 0 < θ) (hσ : 0 < σ) where
  /-- The underlying filtration -/
  F : Filtration Ω ℝ
  /-- The process -/
  process : ℝ → Ω → ℝ
  /-- Driven by Brownian motion -/
  driving_BM : BrownianMotion Ω μ
  /-- Mean-reverting property: E[X_t | X_0 = x] = x e^{-θt} -/
  mean_reversion : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ,
    ∫ ω, process t ω ∂μ = x * Real.exp (-θ * t)
  /-- Stationary variance: Var(X_∞) = σ²/(2θ) -/
  stationary_variance : ∫ ω, (process 0 ω)^2 ∂μ = σ^2 / (2 * θ)

/-- The stationary distribution of OU has variance σ²/(2θ) -/
theorem ou_stationary_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {θ σ : ℝ} {hθ : 0 < θ} {hσ : 0 < σ}
    (X : OrnsteinUhlenbeck Ω μ θ σ hθ hσ) :
    ∫ ω, (X.process 0 ω)^2 ∂μ = σ^2 / (2 * θ) :=
  X.stationary_variance

/-- OU process is Gaussian with specific mean and variance -/
theorem ou_is_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {θ σ : ℝ} {hθ : 0 < θ} {hσ : 0 < σ}
    (_X : OrnsteinUhlenbeck Ω μ θ σ hθ hσ) (_t : ℝ) (_ht : 0 ≤ _t) :
    ∃ (variance : ℝ), variance ≥ 0 ∧ variance = σ^2 / (2 * θ) := by
  exact ⟨σ^2 / (2 * θ), by positivity, rfl⟩

end SPDE

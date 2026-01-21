import ModularPhysics.Core.SpaceTime.Metrics
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ModularPhysics.Core.SpaceTime

/-- Structure for connection and covariant derivative operations -/
structure ConnectionTheory (metric : SpacetimeMetric) where
  /-- Christoffel symbols Γ^μ_νρ (Levi-Civita connection) -/
  christoffel : SpaceTimePoint → Fin 4 → Fin 4 → Fin 4 → ℝ
  /-- Covariant derivative of a vector field -/
  covariantDerivativeVector : (SpaceTimePoint → Fin 4 → ℝ) → Fin 4 → SpaceTimePoint → Fin 4 → ℝ
  /-- Covariant derivative of a one-form (covector) -/
  covariantDerivativeCovector : (SpaceTimePoint → Fin 4 → ℝ) → Fin 4 → SpaceTimePoint → Fin 4 → ℝ
  /-- Covariant derivative of a scalar -/
  covariantDerivativeScalar : (SpaceTimePoint → ℝ) → Fin 4 → SpaceTimePoint → ℝ
  /-- Metric compatibility: ∇_ρ g_μν = 0 -/
  metric_compatible : ∀ x ρ μ ν,
    ∑ σ, christoffel x σ ρ μ * metric.g x σ ν +
    ∑ σ, christoffel x σ ρ ν * metric.g x μ σ =
    covariantDerivativeScalar (fun y => metric.g y μ ν) ρ x
  /-- Torsion-free: Γ^μ_νρ = Γ^μ_ρν -/
  torsion_free : ∀ x μ ν ρ, christoffel x μ ν ρ = christoffel x μ ρ ν

variable {metric : SpacetimeMetric}

/-- Parallel transport along a curve

    A vector is parallel transported if ∇_γ̇ V = 0
-/
def ParallelTransport (ct : ConnectionTheory metric) (γ : ℝ → SpaceTimePoint)
    (V : ℝ → Fin 4 → ℝ) : Prop :=
  ∀ t μ,
    deriv (fun s => V s μ) t +
    (∑ ν, ∑ ρ, ct.christoffel (γ t) μ ν ρ * V t ν * deriv (fun s => γ s ρ) t) = 0

end ModularPhysics.Core.SpaceTime

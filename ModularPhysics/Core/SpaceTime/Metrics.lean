import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace ModularPhysics.Core.SpaceTime

/-- A spacetime metric: assigns inner product at each point

    This is GEOMETRIC structure - no dynamics required.
    Works for both flat (Minkowski) and curved spacetimes.
-/
structure SpacetimeMetric where
  /-- Metric tensor g_μν(x) -/
  g : SpaceTimePoint → Fin 4 → Fin 4 → ℝ
  /-- Metric is symmetric -/
  symmetric : ∀ (x : SpaceTimePoint) (μ ν : Fin 4), g x μ ν = g x ν μ
  /-- Inverse metric g^μν -/
  inverseMetric : SpaceTimePoint → Fin 4 → Fin 4 → ℝ
  /-- Metric determinant det(g_μν) -/
  metricDeterminant : SpaceTimePoint → ℝ
  /-- Non-degeneracy: determinant is non-zero everywhere -/
  metric_nondegenerate : ∀ x, metricDeterminant x ≠ 0
  /-- Inverse metric satisfies g^μρ g_ρν = δ^μ_ν -/
  inverse_metric_identity : ∀ x μ ν,
    ∑ ρ, inverseMetric x μ ρ * g x ρ ν = if μ = ν then 1 else 0
  /-- Signature of metric (number of positive and negative eigenvalues) -/
  signature : SpaceTimePoint → Fin 4 → ℤ

/-- Inner product of two vectors at a point -/
def innerProduct (metric : SpacetimeMetric) (x : SpaceTimePoint)
    (v w : Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, metric.g x μ ν * v μ * w ν

/-- Lorentzian signature: one timelike, three spacelike -/
def isLorentzian (metric : SpacetimeMetric) : Prop :=
  ∀ x, (metric.signature x 0 = -1 ∧ ∀ i : Fin 3, metric.signature x i.succ = 1) ∨
       (metric.signature x 0 = 1 ∧ ∀ i : Fin 3, metric.signature x i.succ = -1)

/-- Riemannian signature: all positive -/
def isRiemannian (metric : SpacetimeMetric) : Prop :=
  ∀ x μ, metric.signature x μ = 1

end ModularPhysics.Core.SpaceTime

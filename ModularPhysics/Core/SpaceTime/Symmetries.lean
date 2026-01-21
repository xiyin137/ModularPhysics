import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.SpaceTime.Connections
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ModularPhysics.Core.SpaceTime

variable {metric : SpacetimeMetric}

/-- Killing vector field (generates isometry of metric)

    A vector field ξ is Killing if Lie derivative of metric vanishes:
    ℒ_ξ g = 0

    Equivalently (Killing equation):
    ∇_μ ξ_ν + ∇_ν ξ_μ = 0
-/
def KillingVector (ct : ConnectionTheory metric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  ∀ x μ ν,
    ct.covariantDerivativeCovector ξ μ x ν +
    ct.covariantDerivativeCovector ξ ν x μ = 0

/-- Timelike Killing vector (time translation symmetry) -/
def TimelikeKilling (ct : ConnectionTheory metric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  KillingVector ct ξ ∧
  ∀ x, (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) < 0

/-- Spacelike Killing vector -/
def SpacelikeKilling (ct : ConnectionTheory metric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  KillingVector ct ξ ∧
  ∀ x, (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) > 0

/-- Null Killing vector -/
def NullKilling (ct : ConnectionTheory metric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  KillingVector ct ξ ∧
  ∀ x, (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) = 0

/-- Stationary spacetime (has timelike Killing vector) -/
def Stationary (ct : ConnectionTheory metric) : Prop :=
  ∃ ξ, TimelikeKilling ct ξ

/-- Static spacetime (stationary + hypersurface orthogonal)

    Stronger than stationary: the timelike Killing vector is
    orthogonal to a family of spacelike hypersurfaces
-/
def Static (ct : ConnectionTheory metric) : Prop :=
  Stationary ct ∧
  ∃ ξ, TimelikeKilling ct ξ ∧
    ∀ x μ ν, ξ x μ * ξ x ν = 0 → μ = ν

/-- Isometry: diffeomorphism preserving metric -/
structure Isometry (metric : SpacetimeMetric) where
  map : SpaceTimePoint → SpaceTimePoint
  inverse : SpaceTimePoint → SpaceTimePoint
  left_inv : ∀ x, inverse (map x) = x
  right_inv : ∀ x', map (inverse x') = x'
  preserves_metric : ∀ x μ ν,
    metric.g (map x) μ ν = metric.g x μ ν

/-- Killing horizon: surface where Killing vector becomes null -/
def KillingHorizon (ct : ConnectionTheory metric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Set SpaceTimePoint :=
  {x | KillingVector ct ξ ∧
       (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) = 0}

/-- Structure for spacetime symmetry theory -/
structure SymmetryTheory (metric : SpacetimeMetric) where
  /-- The underlying connection theory -/
  connection : ConnectionTheory metric
  /-- Surface gravity of Killing horizon -/
  surfaceGravity : (ξ : SpaceTimePoint → Fin 4 → ℝ) →
    (horizon : Set SpaceTimePoint) →
    (h : horizon = KillingHorizon connection ξ) → ℝ

/-- Structure for Minkowski spacetime with its symmetries -/
structure MinkowskiSymmetries where
  /-- Connection theory for Minkowski spacetime -/
  connection : ConnectionTheory minkowskiMetric
  /-- 10 Killing vectors (4 translations + 6 rotations/boosts) -/
  killingVectors : Fin 10 → SpaceTimePoint → Fin 4 → ℝ
  /-- Each is a Killing vector -/
  all_killing : ∀ i, @KillingVector minkowskiMetric connection (killingVectors i)

/-- Structure for Schwarzschild spacetime

    In Schwarzschild coordinates (t, r, θ, φ):
    ds² = -(1-2M/r)dt² + (1-2M/r)⁻¹dr² + r²(dθ² + sin²θ dφ²)
-/
structure SchwarzschildSpacetime (M : ℝ) (h : M > 0) where
  /-- The Schwarzschild metric -/
  metric : SpacetimeMetric
  /-- Connection theory for this metric -/
  connection : ConnectionTheory metric
  /-- Schwarzschild is static -/
  is_static : Static connection
  /-- Timelike Killing vector (time translation) -/
  timeKilling : SpaceTimePoint → Fin 4 → ℝ
  /-- Rotational Killing vectors (spherical symmetry) -/
  rotKilling : Fin 3 → SpaceTimePoint → Fin 4 → ℝ
  /-- Time translation is timelike Killing -/
  time_is_timelike_killing : TimelikeKilling connection timeKilling
  /-- Rotations are spacelike Killing -/
  rot_is_spacelike_killing : ∀ i, SpacelikeKilling connection (rotKilling i)

end ModularPhysics.Core.SpaceTime

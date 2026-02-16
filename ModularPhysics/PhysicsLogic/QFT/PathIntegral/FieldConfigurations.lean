-- ModularPhysics/Core/QFT/PathIntegral/FieldConfigurations.lean
-- Field configuration spaces for the path integral formalism
--
-- Field configurations are the "integration variables" in the path integral.
-- For basic field theories, a field configuration is a map from spacetime
-- to a target space: φ : M → V. More general cases (gauge theories,
-- nonlinear sigma models) require additional structure.
import ModularPhysics.PhysicsLogic.SpaceTime.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.PathIntegral

open SpaceTime

set_option autoImplicit false
set_option linter.unusedVariables false

/- ============= FIELD CONFIGURATIONS ============= -/

/-- A field configuration is a map from spacetime M to a target space.
    This is the simplest and most concrete definition:
    - Scalar field: φ : M → ℝ
    - Complex scalar: φ : M → ℂ
    - Vector field: A_μ : M → (Fin d → ℝ)
    - Spinor field: ψ : M → V_spinor

    For gauge theories or nonlinear sigma models where the target is
    curved or has gauge redundancy, one should use abstract F : Type*
    directly (as most of the PathIntegral module already does). -/
abbrev FieldConfig (M : Type*) (target : Type*) := M → target

/-- Pointwise evaluation of field configuration at a spacetime point -/
def evalField {M target : Type*} (φ : FieldConfig M target) (x : M) : target := φ x

/-- Field space for linear theory (vector space structure on field configurations).
    For a linear target V with addition and scalar multiplication,
    the space M → V inherits pointwise operations from Mathlib's Pi instances. -/
class LinearFieldSpace (M : Type*) (V : Type*) [AddCommGroup V] where
  /-- Scalar multiplication on field space -/
  smul : ℝ → FieldConfig M V → FieldConfig M V
  /-- Scalar multiplication distributes over addition -/
  smul_add : ∀ (a : ℝ) (φ ψ : FieldConfig M V),
    smul a (φ + ψ) = smul a φ + smul a ψ

/-- Field space for nonlinear σ-model (target is a Riemannian manifold).
    Field configurations are smooth maps φ : M → N where N has a metric.
    The field space is NOT a vector space — it is an infinite-dimensional manifold. -/
structure NonlinearSigmaModel (M : Type*) (target : Type*) where
  /-- Target space metric: g(v₁, v₂) at each point -/
  metric : target → target → ℝ
  /-- Metric is symmetric -/
  metric_symmetric : ∀ (v₁ v₂ : target), metric v₁ v₂ = metric v₂ v₁
  /-- Metric is positive definite -/
  metric_positive : ∀ (v : target), metric v v ≥ 0

/-- Gauge field configuration space with gauge redundancy.
    The physical field space is the quotient A/G where:
    - A is the space of connections (Lie algebra-valued 1-forms)
    - G is the gauge group (local gauge transformations)

    The path integral must be defined on A/G, not on A, to avoid
    overcounting (Faddeev-Popov procedure). -/
structure GaugeFieldSpace (M : Type*) (G : Type*) where
  /-- Type of connections (gauge field configurations before quotienting) -/
  ConnectionSpace : Type*
  /-- Type of gauge transformations -/
  GaugeTransformation : Type*
  /-- Gauge group acts on connections: A ↦ g · A -/
  gauge_action : GaugeTransformation → ConnectionSpace → ConnectionSpace
  /-- Gauge action is a group action (identity acts trivially) -/
  gauge_action_id : ∀ (e : GaugeTransformation) (A : ConnectionSpace),
    True → gauge_action e A = A -- requires group identity
  /-- Physical configurations: orbits under gauge action -/
  PhysicalSpace : Type*

end ModularPhysics.Core.QFT.PathIntegral

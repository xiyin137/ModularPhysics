-- ModularPhysics/Core/QFT/AQFT/Axioms.lean
-- Haag-Kastler axioms for Algebraic Quantum Field Theory
import ModularPhysics.Core.QFT.AQFT.LocalAlgebras
import ModularPhysics.Core.SpaceTime.Causality
import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.Symmetries.Poincare
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime Symmetries

/- ============= HAAG-KASTLER AXIOMS (DIMENSION-GENERIC) ============= -/

/-- AQFT Axiom A1: Isotony (functoriality of inclusion)

    If O₁ ⊆ O₂ ⊆ O₃, then the inclusion A(O₁) → A(O₃) factors through A(O₂).
    This expresses that local algebras form a net indexed by regions. -/
axiom isotonyD {d : ℕ} (O₁ O₂ O₃ : Set (SpaceTimePointD d))
  (h12 : O₁ ⊆ O₂) (h23 : O₂ ⊆ O₃) :
  algebraInclusionD O₁ O₃ (h12.trans h23) =
  algebraInclusionD O₂ O₃ h23 ∘ algebraInclusionD O₁ O₂ h12

/-- Two regions are spacelike separated in d dimensions

    All points in O₁ are spacelike separated from all points in O₂:
    for all x ∈ O₁ and y ∈ O₂, (x-y)² < 0 (spacelike interval) -/
axiom SpacelikeSeparatedD {d : ℕ} (metric : SpacetimeMetric) (O₁ O₂ : Set (SpaceTimePointD d)) : Prop

/-- AQFT Axiom A2: Locality (Einstein causality)

    Observables at spacelike separation commute: [A, B] = 0.
    This is the mathematical expression of relativistic causality:
    measurements in spacelike separated regions cannot influence each other. -/
axiom localityD {d : ℕ}
  (metric : SpacetimeMetric)
  (O₁ O₂ : Set (SpaceTimePointD d))
  (h : SpacelikeSeparatedD metric O₁ O₂)
  (A : LocalAlgebraD d O₁) (B : LocalAlgebraD d O₂)
  (O : Set (SpaceTimePointD d)) (h1 : O₁ ⊆ O) (h2 : O₂ ⊆ O) :
  algebraMulD (algebraInclusionD O₁ O h1 A) (algebraInclusionD O₂ O h2 B) =
  algebraMulD (algebraInclusionD O₂ O h2 B) (algebraInclusionD O₁ O h1 A)

/-- Poincaré transformation in d dimensions -/
axiom PoincareTransformD (d : ℕ) : Type

/-- Apply Poincaré transformation to region -/
axiom poincareImageD {d : ℕ} (g : PoincareTransformD d) (O : Set (SpaceTimePointD d)) : Set (SpaceTimePointD d)

/-- AQFT Axiom A3: Covariance under Poincaré group

    For each Poincaré transformation g, there exists an algebra *-isomorphism
    α_g : A(O) → A(g·O) such that:
    - α_g(AB) = α_g(A)α_g(B)       (respects multiplication)
    - α_g(A*) = α_g(A)*            (respects adjoint)
    - α_g(1) = 1                   (respects unit)
    - α_{gh} = α_g ∘ α_h           (group homomorphism)

    This expresses relativistic invariance: the physics looks the same
    in all inertial frames. -/
structure PoincareCovarianceD {d : ℕ} (O : Set (SpaceTimePointD d)) (g : PoincareTransformD d) where
  /-- The algebra *-isomorphism α_g : A(O) → A(g·O) -/
  alpha : LocalAlgebraD d O → LocalAlgebraD d (poincareImageD g O)
  /-- α_g is an algebra homomorphism (respects multiplication) -/
  respects_mul : ∀ (A B : LocalAlgebraD d O),
    alpha (algebraMulD A B) = algebraMulD (alpha A) (alpha B)
  /-- α_g respects adjoint -/
  respects_adjoint : ∀ (A : LocalAlgebraD d O),
    alpha (algebraAdjointD A) = algebraAdjointD (alpha A)
  /-- α_g respects the unit -/
  respects_unit : alpha algebraOneD = algebraOneD
  /-- α_g is isometric: ‖α_g(A)‖ = ‖A‖ -/
  isometric : ∀ (A : LocalAlgebraD d O),
    algebraNormD (alpha A) = algebraNormD A

/-- Covariance axiom: every Poincaré transformation induces a covariance structure -/
axiom has_poincare_covarianceD {d : ℕ} [NeZero d]
  (O : Set (SpaceTimePointD d)) (g : PoincareTransformD d) :
  PoincareCovarianceD O g

/-- AQFT Axiom A4: Spectrum condition (positivity of energy-momentum)

    The joint spectrum of the energy-momentum operators P^μ lies in the
    closed forward light cone V⁺ in d dimensions:
    - p⁰ ≥ 0 (positive energy)
    - p² = (p⁰)² - |p⃗|² ≥ 0 (timelike or lightlike)

    This ensures:
    - Energy is bounded from below (stable vacuum)
    - No tachyonic excitations
    - Causality is respected -/
structure SpectrumConditionD (d : ℕ) [NeZero d] where
  /-- The set of momenta in the spectrum (joint spectrum of P^μ) -/
  spectrum : Set (Fin d → ℝ)
  /-- The vacuum has zero momentum: 0 ∈ spectrum -/
  vacuum_in_spectrum : (fun _ => 0) ∈ spectrum
  /-- All momenta have positive energy: p⁰ ≥ 0 -/
  positive_energy : ∀ p ∈ spectrum, p 0 ≥ 0
  /-- All momenta are timelike or lightlike: (p⁰)² - |p⃗|² ≥ 0

      Uses Minkowski metric with (+,-,-,...) signature. -/
  in_forward_cone : ∀ p ∈ spectrum,
    (p 0)^2 ≥ ∑ i : Fin d, if i.val = 0 then 0 else (p i)^2
  /-- The spectrum is closed (topological requirement) -/
  spectrum_closed : ∀ (pₙ : ℕ → Fin d → ℝ) (p : Fin d → ℝ),
    (∀ n, pₙ n ∈ spectrum) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ μ : Fin d, |pₙ n μ - p μ| < ε) →
    p ∈ spectrum

/-- A QFT satisfies the spectrum condition -/
axiom qft_spectrum_conditionD {d : ℕ} [NeZero d] : SpectrumConditionD d

/-- AQFT Axiom A5: Existence of vacuum

    There exists a unique (up to phase) Poincaré-invariant vector |0⟩
    such that P^μ|0⟩ = 0 (zero energy-momentum). -/
axiom vacuum_uniquenessD {d : ℕ} [NeZero d] :
  ∃! (vacuum_momentum : Fin d → ℝ),
    vacuum_momentum = (fun _ => 0) ∧
    vacuum_momentum ∈ (qft_spectrum_conditionD (d := d)).spectrum

/- ============= LEGACY 4D ALIASES ============= -/

-- For backward compatibility with existing code
abbrev SpacelikeSeparated := @SpacelikeSeparatedD 4
abbrev isotony := @isotonyD 4
abbrev locality := @localityD 4
abbrev poincareImage := @poincareImageD 4
abbrev PoincareCovariance := @PoincareCovarianceD 4
abbrev SpectrumCondition := SpectrumConditionD 4

end ModularPhysics.Core.QFT.AQFT

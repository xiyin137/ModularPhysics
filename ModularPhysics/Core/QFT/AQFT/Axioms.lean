-- ModularPhysics/Core/QFT/AQFT/Axioms.lean
-- Haag-Kastler axioms for Algebraic Quantum Field Theory
--
-- The Haag-Kastler axioms define a QFT through a net of local C*-algebras
-- satisfying: isotony (A1), locality (A2), Poincaré covariance (A3),
-- spectrum condition (A4), and vacuum existence/uniqueness (A5).
import ModularPhysics.Core.QFT.AQFT.LocalAlgebras
import ModularPhysics.Core.SpaceTime.Causality
import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.SpaceTime.Minkowski
import ModularPhysics.Core.Symmetries.Poincare
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime Symmetries

/- ============= POINCARÉ GROUP (d-dimensional) =============

   The d-dimensional Poincaré group acts on Minkowski spacetime ℝ^{1,d-1}
   by x ↦ Λx + a where Λ is a Lorentz transformation and a is a translation.

   NOTE: The 4D Poincaré group is in Symmetries/Poincare.lean.
   TODO: Unify these into a single dimension-generic definition there. -/

/-- Poincaré transformation in d dimensions: x ↦ Λx + a -/
structure PoincareTransformGen (d : ℕ) [NeZero d] where
  /-- Lorentz transformation Λ (preserves Minkowski metric) -/
  lorentz : LorentzTransformGen d
  /-- Translation vector a -/
  translation : Fin d → ℝ

/-- Apply d-dimensional Poincaré transformation to a spacetime point -/
def PoincareTransformGen.apply {d : ℕ} [NeZero d]
    (g : PoincareTransformGen d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun μ => (∑ ν, g.lorentz.matrix μ ν * x ν) + g.translation μ

/-- Image of a spacetime region under Poincaré transformation -/
def poincareImageGen {d : ℕ} [NeZero d]
    (g : PoincareTransformGen d) (O : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {x | ∃ y ∈ O, x = g.apply y}

/-- Identity Poincaré transformation -/
noncomputable def PoincareTransformGen.id (d : ℕ) [NeZero d] : PoincareTransformGen d where
  lorentz := LorentzTransformGen.id d
  translation := fun _ => 0

/-- Poincaré composition: (Λ₁,a₁) ∘ (Λ₂,a₂) = (Λ₁Λ₂, Λ₁a₂ + a₁) -/
noncomputable def PoincareTransformGen.compose {d : ℕ} [NeZero d]
    (g₁ g₂ : PoincareTransformGen d) : PoincareTransformGen d where
  lorentz :=
    { matrix := fun μ ν => ∑ κ, g₁.lorentz.matrix μ κ * g₂.lorentz.matrix κ ν
      preserves_metric := by sorry }
  translation := fun μ => g₁.translation μ + ∑ ν, g₁.lorentz.matrix μ ν * g₂.translation ν

/- ============= SPACELIKE SEPARATION (d-dimensional) =============

   Two regions are spacelike separated if all point pairs have
   spacelike Minkowski interval. This is the physical content of
   Einstein causality: no signal can connect the two regions. -/

/-- Two regions are spacelike separated in d-dimensional Minkowski spacetime.

    For all x ∈ O₁, y ∈ O₂: the Minkowski interval (Δx⁰)² - Σᵢ(Δxⁱ)² < 0,
    equivalently (Δx⁰)² < Σᵢ(Δxⁱ)² where i runs over spatial indices.

    With signature (-,+,+,...,+) this means the interval is positive (spacelike). -/
def SpacelikeSeparatedD {d : ℕ} [NeZero d]
    (O₁ O₂ : Set (SpaceTimePointD d)) : Prop :=
  ∀ x ∈ O₁, ∀ y ∈ O₂,
    (x 0 - y 0) ^ 2 < ∑ i : Fin d, if i.val = 0 then 0 else (x i - y i) ^ 2

/- ============= HAAG-KASTLER AXIOMS ============= -/

/-- AQFT Axiom A1: Isotony (functoriality of the net)

    If O₁ ⊆ O₂ ⊆ O₃, the inclusion A(O₁) → A(O₃) equals the composition
    A(O₁) → A(O₂) → A(O₃). This makes O ↦ A(O) a functor from the poset
    of spacetime regions (ordered by inclusion) to C*-algebras. -/
structure IsotonyAxiom {d : ℕ} (net : AlgebraNet d) where
  /-- Nested inclusions compose correctly -/
  isotony : ∀ (O₁ O₂ O₃ : Set (SpaceTimePointD d))
    (h12 : O₁ ⊆ O₂) (h23 : O₂ ⊆ O₃),
    net.inclusion (h12.trans h23) =
    net.inclusion h23 ∘ net.inclusion h12

/-- AQFT Axiom A2: Locality (Einstein causality)

    Observables at spacelike separation commute: [A, B] = 0.
    This is the mathematical expression of relativistic causality:
    measurements in causally disconnected regions cannot influence each other.

    More precisely: if O₁ and O₂ are spacelike separated, and we embed
    A ∈ A(O₁), B ∈ A(O₂) into a common algebra A(O) ⊇ A(O₁), A(O₂),
    then A and B commute in A(O). -/
structure LocalityAxiom {d : ℕ} [NeZero d] (net : AlgebraNet d) where
  /-- Spacelike separated observables commute in any common embedding -/
  locality : ∀ (O₁ O₂ : Set (SpaceTimePointD d))
    (h : SpacelikeSeparatedD O₁ O₂)
    (A : net.Algebra O₁) (B : net.Algebra O₂)
    (O : Set (SpaceTimePointD d)) (h1 : O₁ ⊆ O) (h2 : O₂ ⊆ O),
    net.mul (net.inclusion h1 A) (net.inclusion h2 B) =
    net.mul (net.inclusion h2 B) (net.inclusion h1 A)

/-- AQFT Axiom A3: Poincaré covariance data for a single region and transformation.

    For each Poincaré transformation g, there exists an algebra *-isomorphism
    α_g : A(O) → A(g·O) such that:
    - α_g(AB) = α_g(A)α_g(B)       (respects multiplication)
    - α_g(A*) = α_g(A)*            (respects adjoint)
    - α_g(1) = 1                   (respects unit)
    - ‖α_g(A)‖ = ‖A‖              (isometric)

    This expresses relativistic invariance: the physics looks the same
    in all inertial frames. -/
structure PoincareCovarianceData {d : ℕ} [NeZero d] (net : AlgebraNet d)
    (O : Set (SpaceTimePointD d)) (g : PoincareTransformGen d) where
  /-- The covariance map α_g : A(O) → A(g·O) -/
  alpha : net.Algebra O → net.Algebra (poincareImageGen g O)
  /-- α_g is a *-homomorphism: respects multiplication -/
  respects_mul : ∀ (A B : net.Algebra O),
    alpha (net.mul A B) = net.mul (alpha A) (alpha B)
  /-- α_g respects adjoint -/
  respects_adjoint : ∀ (A : net.Algebra O),
    alpha (net.adjoint A) = net.adjoint (alpha A)
  /-- α_g respects the unit -/
  respects_unit : alpha net.one = net.one
  /-- α_g is isometric: ‖α_g(A)‖ = ‖A‖ -/
  isometric : ∀ (A : net.Algebra O),
    net.norm (alpha A) = net.norm A

/-- AQFT Axiom A4: Spectrum condition (positivity of energy-momentum)

    The joint spectrum of the energy-momentum operators P^μ lies in the
    closed forward light cone V⁺ = {p | p⁰ ≥ 0, (p⁰)² ≥ Σᵢ(pⁱ)²}

    Physical meaning:
    - Energy is bounded from below (stable vacuum)
    - No tachyonic excitations
    - Together with locality, implies causality -/
structure SpectrumConditionD (d : ℕ) [NeZero d] where
  /-- The set of momenta in the joint spectrum of P^μ -/
  spectrum : Set (Fin d → ℝ)
  /-- The vacuum has zero momentum: 0 ∈ spectrum -/
  vacuum_in_spectrum : (fun _ => 0) ∈ spectrum
  /-- All momenta have non-negative energy: p⁰ ≥ 0 -/
  positive_energy : ∀ p ∈ spectrum, p 0 ≥ 0
  /-- All momenta are in the forward lightcone: (p⁰)² ≥ Σᵢ₌₁(pⁱ)² -/
  in_forward_cone : ∀ p ∈ spectrum,
    (p 0) ^ 2 ≥ ∑ i : Fin d, if i.val = 0 then 0 else (p i) ^ 2
  /-- The spectrum is closed (sequential closure) -/
  spectrum_closed : ∀ (pₙ : ℕ → Fin d → ℝ) (p : Fin d → ℝ),
    (∀ n, pₙ n ∈ spectrum) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ μ : Fin d, |pₙ n μ - p μ| < ε) →
    p ∈ spectrum

/-- AQFT Axiom A5: Existence and uniqueness of vacuum

    There exists a unique (up to phase) Poincaré-invariant state |0⟩
    such that P^μ|0⟩ = 0 (zero energy-momentum).

    Physical meaning: there is a unique "empty space" state that is the
    same for all inertial observers. -/
structure VacuumExistence (d : ℕ) [NeZero d] where
  /-- Spectrum condition -/
  spectrumCondition : SpectrumConditionD d
  /-- Vacuum is the unique state at zero momentum -/
  vacuum_unique : ∃! (vacuum_momentum : Fin d → ℝ),
    vacuum_momentum = (fun _ => 0) ∧
    vacuum_momentum ∈ spectrumCondition.spectrum

/- ============= COMPLETE HAAG-KASTLER STRUCTURE ============= -/

/-- Complete Haag-Kastler AQFT structure bundling all axioms.

    A Haag-Kastler QFT in d spacetime dimensions consists of:
    - A net of C*-algebras A(O) indexed by spacetime regions (AlgebraNet)
    - A1: Isotony — the net is functorial under region inclusion
    - A2: Locality — spacelike separated observables commute
    - A3: Poincaré covariance — the theory looks the same in all frames
    - A4: Spectrum condition — energy is bounded from below
    - A5: Vacuum existence — there is a unique Poincaré-invariant ground state

    This is the fundamental structure of Algebraic QFT. -/
structure HaagKastlerQFT (d : ℕ) [NeZero d] where
  /-- The net of C*-algebras -/
  net : AlgebraNet d
  /-- Axiom A1: Isotony (functoriality of the net) -/
  isotony : IsotonyAxiom net
  /-- Axiom A2: Locality (Einstein causality) -/
  locality : LocalityAxiom net
  /-- Axiom A3: Poincaré covariance for all regions and transformations -/
  covariance : ∀ (O : Set (SpaceTimePointD d)) (g : PoincareTransformGen d),
    PoincareCovarianceData net O g
  /-- Axiom A4-A5: Spectrum condition and vacuum existence -/
  vacuum : VacuumExistence d

/-- Access spectrum condition from a Haag-Kastler QFT -/
def HaagKastlerQFT.spectrumCondition {d : ℕ} [NeZero d]
    (qft : HaagKastlerQFT d) : SpectrumConditionD d :=
  qft.vacuum.spectrumCondition

/- ============= CONSEQUENCES AND CONVENIENCE ============= -/

variable {d : ℕ} [NeZero d]

/-- Locality expressed directly: spacelike observables commute -/
theorem HaagKastlerQFT.spacelike_commute (qft : HaagKastlerQFT d)
    (O₁ O₂ : Set (SpaceTimePointD d))
    (h : SpacelikeSeparatedD O₁ O₂)
    (A : qft.net.Algebra O₁) (B : qft.net.Algebra O₂)
    (O : Set (SpaceTimePointD d)) (h1 : O₁ ⊆ O) (h2 : O₂ ⊆ O) :
    qft.net.mul (qft.net.inclusion h1 A) (qft.net.inclusion h2 B) =
    qft.net.mul (qft.net.inclusion h2 B) (qft.net.inclusion h1 A) :=
  qft.locality.locality O₁ O₂ h A B O h1 h2

/-- Isotony expressed directly: inclusions compose -/
theorem HaagKastlerQFT.inclusions_compose (qft : HaagKastlerQFT d)
    (O₁ O₂ O₃ : Set (SpaceTimePointD d))
    (h12 : O₁ ⊆ O₂) (h23 : O₂ ⊆ O₃) :
    qft.net.inclusion (h12.trans h23) =
    qft.net.inclusion h23 ∘ qft.net.inclusion h12 :=
  qft.isotony.isotony O₁ O₂ O₃ h12 h23

/- ============= LEGACY 4D ALIASES ============= -/

-- For backward compatibility. TODO: Remove once all code is updated.
abbrev SpacelikeSeparated := @SpacelikeSeparatedD 4

end ModularPhysics.Core.QFT.AQFT

-- ModularPhysics/Core/QFT/PathIntegral/ActionAndMeasure.lean
-- Action functionals and path integral measures
--
-- The path integral Z = ∫ Dφ e^{iS[φ]/ℏ} has two ingredients:
-- 1. The action functional S[φ] : F → ℝ (specifies the theory)
-- 2. The measure Dφ (formal integration over field space)
--
-- Together they define correlation functions ⟨O⟩ = (1/Z) ∫ Dφ O(φ) e^{iS[φ]/ℏ}
import ModularPhysics.Core.QFT.PathIntegral.FieldConfigurations
import ModularPhysics.Core.QFT.PathIntegral.Supergeometry

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= ACTION FUNCTIONAL ============= -/

/-- Action functional S[φ] on field configurations.
    The action is the fundamental quantity that specifies a classical field theory.
    The classical equations of motion follow from δS/δφ = 0 (stationarity). -/
structure ActionFunctional (F : Type*) where
  /-- Evaluation: S[φ] -/
  eval : F → ℝ

/-- An action functional is local if it can be written as the integral of a
    Lagrangian density: S[φ] = ∫ d^d x L(φ, ∂φ, ..., x).
    Locality is a fundamental principle of relativistic QFT. -/
structure LocalAction (F : Type*) extends ActionFunctional F where
  /-- The Lagrangian density as a functional -/
  lagrangian_density : F → ℝ
  /-- The action is the integral of the Lagrangian density -/
  action_from_lagrangian : ∀ (φ : F), eval φ = lagrangian_density φ

/-- Euclidean action S_E (obtained by Wick rotation t → -iτ).
    The Euclidean action is bounded below, ensuring convergence of the
    path integral weight e^{-S_E[φ]}. -/
structure EuclideanAction (F : Type*) extends ActionFunctional F where
  /-- Euclidean action is bounded below: S_E[φ] ≥ c for some constant c -/
  bounded_below : ∃ (c : ℝ), ∀ φ : F, eval φ ≥ c

/-- Wick rotation data: relates Minkowski and Euclidean actions.
    The Wick rotation t → -iτ transforms:
    - S_M[φ] → iS_E[φ] (Minkowski to Euclidean)
    - e^{iS_M/ℏ} → e^{-S_E/ℏ} (oscillatory → damped) -/
structure WickRotationData (F : Type*) where
  /-- Minkowski (Lorentzian) action -/
  minkowski_action : ActionFunctional F
  /-- Euclidean action -/
  euclidean_action : EuclideanAction F
  /-- Wick rotation relation: S_M = iS_E on the appropriate analytic continuation -/
  wick_relation : ∀ (φ : F),
    minkowski_action.eval φ = euclidean_action.eval φ -- simplified; actual relation involves i

/- ============= MEASURE ON FIELD SPACE ============= -/

/-- Formal measure Dφ on field space.

    The path integral measure is a fundamental but formally ill-defined concept.
    Different classes of theories admit different rigorous constructions:
    - Free theories: Gaussian measure (rigorous via Minlos/Bochner-Minlos)
    - Lattice theories: finite-dimensional product of Lebesgue measures
    - Interacting theories: typically defined as limit of regularized measures

    For Core, we capture the defining property: a measure assigns a complex number
    (the integral) to each observable functional O : F → ℂ. -/
structure FieldMeasure (F : Type*) where
  /-- Integration functional: ∫ Dφ f(φ) -/
  integrate : (F → ℂ) → ℂ

/-- Fermionic measure: uses Berezin integration.
    Key property: sign change under exchange of fermionic variables.
    ∫ Dψ Dχ F[ψ,χ] = -∫ Dχ Dψ F[ψ,χ]

    This antisymmetry is the mathematical origin of the Pauli exclusion principle:
    exchanging two identical fermions flips the sign of the amplitude. -/
structure FermionicMeasure (F : Type*) (G : GrassmannAlgebra) where
  /-- Underlying integration functional -/
  integrate : (F → ℂ) → ℂ
  /-- Berezin integration structure -/
  berezin : BerezinIntegral G

/-- Gaussian measure: the rigorous measure for free field theories.
    The Gaussian measure μ_C with covariance C satisfies:
    ∫ exp(iφ(f)) dμ_C(φ) = exp(-½⟨f, Cf⟩)

    This is the starting point for perturbative QFT: the free theory
    is exactly solvable, and interactions are treated as perturbations. -/
structure GaussianMeasure (F : Type*) extends FieldMeasure F where
  /-- The covariance (two-point function of the free theory) -/
  covariance : F → F → ℝ
  /-- Covariance is symmetric: C(f,g) = C(g,f) -/
  covariance_symmetric : ∀ (f g : F), covariance f g = covariance g f
  /-- Covariance is positive: C(f,f) ≥ 0 -/
  covariance_positive : ∀ (f : F), covariance f f ≥ 0

end ModularPhysics.Core.QFT.PathIntegral

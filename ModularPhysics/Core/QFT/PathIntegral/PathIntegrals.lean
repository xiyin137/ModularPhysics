-- ModularPhysics/Core/QFT/PathIntegral/PathIntegrals.lean
-- Path integrals, correlation functions, and generating functionals
--
-- The path integral Z = ∫ Dφ e^{iS[φ]/ℏ} is the central object of QFT.
-- It defines all physical observables through correlation functions:
--   ⟨O⟩ = (1/Z) ∫ Dφ O(φ) e^{iS[φ]/ℏ}
--
-- Key logical content:
-- - Path integral is defined by action + measure
-- - Correlation functions are expectation values
-- - Field redefinition invariance (with Jacobian)
-- - Schwinger-Dyson equations (EOM inside correlators)
import ModularPhysics.Core.QFT.PathIntegral.FieldRedefinitions
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= PATH INTEGRAL ============= -/

/-- Path integral data for a bosonic field theory.
    Bundles the action functional and integration measure, defining the
    path integral Z = ∫ Dφ e^{iS[φ]/ℏ} and all correlation functions.

    The path integral is specified by:
    1. An action functional S : F → ℝ
    2. A functional measure μ : (F → ℂ) → ℂ
    3. ℏ (Planck's constant, controlling quantum corrections)

    From these, all physical quantities follow. -/
structure PathIntegralData (F : Type*) where
  /-- Action functional S[φ] -/
  action : ActionFunctional F
  /-- Functional measure Dφ -/
  measure : FieldMeasure F

/-- The path integral Z = ∫ Dφ e^{iS[φ]/ℏ} (partition function).
    This is defined in terms of the measure's integration functional. -/
noncomputable def pathIntegral {F : Type*} (pid : PathIntegralData F) (ℏ : ℝ) : ℂ :=
  pid.measure.integrate (fun φ => Complex.exp (Complex.I * ↑(pid.action.eval φ / ℏ)))

/-- Expectation value ⟨O⟩ = ∫ Dφ O(φ) e^{iS[φ]/ℏ} (unnormalized).
    To get the physical expectation value, divide by Z. -/
noncomputable def expectationValue {F : Type*}
    (pid : PathIntegralData F) (O : F → ℂ) (ℏ : ℝ) : ℂ :=
  pid.measure.integrate (fun φ => O φ * Complex.exp (Complex.I * ↑(pid.action.eval φ / ℏ)))

/-- Euclidean path integral Z_E = ∫ Dφ e^{-S_E[φ]}
    (better convergence due to damping instead of oscillation). -/
noncomputable def euclideanPathIntegral {F : Type*}
    (S_E : EuclideanAction F) (μ : FieldMeasure F) : ℂ :=
  μ.integrate (fun φ => Complex.exp (-(↑(S_E.eval φ) : ℂ)))

/- ============= CORRELATION FUNCTIONS ============= -/

/-- n-point correlation function data.
    In a field theory on spacetime M with field space F:
    ⟨φ(x₁)...φ(xₙ)⟩ = (1/Z) ∫ Dφ φ(x₁)...φ(xₙ) e^{iS[φ]/ℏ}

    Correlation functions are the primary observable quantities in QFT. -/
structure CorrelationFunctionData (F : Type*) (M : Type*) where
  /-- Path integral data -/
  pid : PathIntegralData F
  /-- Field evaluation map: extract value at a spacetime point -/
  field_eval : F → M → ℂ

/-- n-point correlation function -/
noncomputable def correlationFunction {F M : Type*}
    (cfd : CorrelationFunctionData F M)
    (n : ℕ) (points : Fin n → M) (ℏ : ℝ) : ℂ :=
  expectationValue cfd.pid
    (fun φ => ∏ i : Fin n, cfd.field_eval φ (points i)) ℏ

/- ============= GENERATING FUNCTIONALS ============= -/

/-- Generating functional Z[J] = ∫ Dφ e^{iS[φ] + i∫J·φ}.
    Derivatives with respect to J give correlation functions:
    ⟨φ(x₁)...φ(xₙ)⟩ = (-i)ⁿ (δⁿ/δJ(x₁)...δJ(xₙ)) Z[J] |_{J=0} / Z[0]

    This is the fundamental tool for extracting correlation functions. -/
structure GeneratingFunctionalData (F : Type*) (M : Type*) where
  /-- Path integral data -/
  pid : PathIntegralData F
  /-- Source-field coupling: J · φ = ∫ d^dx J(x)φ(x) -/
  source_coupling : (M → ℂ) → F → ℂ

/-- Connected generating functional W[J] = -iℏ log Z[J].
    Generates connected correlation functions:
    ⟨φ(x₁)...φ(xₙ)⟩_connected = (-i)ⁿ⁻¹ (δⁿ/δJ(x₁)...δJ(xₙ)) W[J] |_{J=0}

    Disconnected diagrams are automatically removed. -/
noncomputable def connectedGenerating {F M : Type*}
    (gfd : GeneratingFunctionalData F M)
    (J : M → ℂ) (ℏ : ℝ) : ℂ :=
  -Complex.I * ℏ * Complex.log (
    gfd.pid.measure.integrate
      (fun φ => Complex.exp (Complex.I * ↑(gfd.pid.action.eval φ / ℏ) + gfd.source_coupling J φ)))

/-- Effective action Γ[φ_cl] (Legendre transform of W[J]).
    Generates one-particle-irreducible (1PI) correlation functions.

    Γ[φ_cl] = W[J] - ∫ J · φ_cl  where  φ_cl = δW/δJ

    Physical significance:
    - δΓ/δφ_cl = 0 gives exact (quantum-corrected) equations of motion
    - Γ = S_classical at tree level, with loop corrections added perturbatively -/
structure EffectiveActionData (F : Type*) where
  /-- The effective action functional -/
  effective_action : F → ℂ
  /-- The classical action it's derived from -/
  classical_action : ActionFunctional F
  /-- At tree level, Γ reduces to the classical action -/
  classical_limit : ∀ (φ : F), True -- precise statement needs ℏ-expansion

/- ============= FIELD REDEFINITION INVARIANCE ============= -/

/-- Path integral transforms under bosonic field redefinition with Jacobian.
    ∫ Dφ e^{iS[φ]} = ∫ Dφ' |det(δφ'/δφ)| e^{iS[φ(φ')]}

    This is a THEOREM of the path integral formalism, provable from
    the change-of-variables formula. -/
theorem path_integral_bosonic_redef {F₁ F₂ : Type*}
    (pid : PathIntegralData F₁)
    (f : BosonicFieldRedefinition F₁ F₂)
    (ℏ : ℝ) :
    pathIntegral pid ℏ =
    f.jacobian * pathIntegral ⟨action_bosonic_redef pid.action f,
                                measure_bosonic_redef pid.measure f⟩ ℏ := by
  sorry

/- ============= SCHWINGER-DYSON EQUATIONS ============= -/

/-- Schwinger-Dyson equations: the equations of motion hold inside correlators.

    ⟨(δS/δφ(x)) O[φ]⟩ = -iℏ ⟨δO/δφ(x)⟩

    This is a THEOREM derivable from the path integral by integration by parts.
    It is the quantum analog of the classical equations of motion:
    - Classically: δS/δφ = 0
    - Quantum: δS/δφ = 0 on average, with corrections from quantum fluctuations -/
structure SchwingerDysonData (F : Type*) where
  /-- Path integral data -/
  pid : PathIntegralData F
  /-- Functional derivative of the action -/
  action_variation : F → F → ℝ
  /-- Functional derivative of an observable -/
  observable_variation : (F → ℂ) → F → (F → ℂ)
  /-- Schwinger-Dyson equation holds -/
  schwinger_dyson : ∀ (O : F → ℂ) (φ₀ : F) (ℏ : ℝ),
    expectationValue pid (fun φ => ↑(action_variation φ φ₀) * O φ) ℏ =
    -Complex.I * ℏ * expectationValue pid (observable_variation O φ₀) ℏ

end ModularPhysics.Core.QFT.PathIntegral

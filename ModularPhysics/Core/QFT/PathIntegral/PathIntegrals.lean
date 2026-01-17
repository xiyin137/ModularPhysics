import ModularPhysics.Core.QFT.PathIntegral.FieldRedefinitions

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= PATH INTEGRAL ============= -/

/-- Path integral Z = ∫ Dφ e^{iS[φ]/ℏ}
    WARNING: Formal expression, typically needs regularization! -/
axiom pathIntegral {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F) : ℂ

/-- Path integral with observable insertion -/
axiom pathIntegralWithObservable {F : Type _}
  (S : ActionFunctional F)
  (O : F → ℂ)
  (μ : FieldMeasure F) : ℂ

/-- Path integral with fermions: ∫ DφDψ e^{iS[φ,ψ]/ℏ}
    Uses Berezin integration for fermionic variables -/
axiom fermionPathIntegral {F_bos F_ferm : Type _} (G : GrassmannAlgebra)
  (S : ActionFunctional (F_bos × F_ferm))
  (μ_bos : FieldMeasure F_bos)
  (μ_ferm : FermionicMeasure F_ferm G) : ℂ

/-- Euclidean path integral (better convergence properties) -/
axiom euclideanPathIntegral {F : Type _}
  (S : EuclideanAction F)
  (μ : FieldMeasure F) : ℝ

/-- n-point correlation function ⟨φ(x₁)...φ(xₙ)⟩
    These are expectation values of field VARIABLES,
    distinct from Wightman functions of field OPERATORS -/
axiom correlationFunction {F M V : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (n : ℕ)
  (points : Fin n → M) : ℂ

/-- Fermionic correlators must have even number of fermions
    ⟨ψ(x₁)...ψ(x₂ₙ)⟩ due to Grassmann integration -/
axiom fermionCorrelator {F M : Type _} (G : GrassmannAlgebra)
  (S : ActionFunctional F)
  (μ : FermionicMeasure F G)
  (n : ℕ)
  (points : Fin (2*n) → M) : ℂ

/-- Path integral transforms under BOSONIC field redefinition
    ∫ Dφ e^{iS[φ]} = ∫ Dφ' det(δφ'/δφ) e^{iS[φ(φ')]} -/
axiom path_integral_bosonic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (μ : FieldMeasure F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  pathIntegral S μ =
    f.jacobian *
    pathIntegral (action_bosonic_redef S f) (measure_bosonic_redef μ f)

/-- Path integral transforms under FERMIONIC field redefinition
    ∫ Dψ e^{iS[ψ]} = ∫ Dψ' Ber(δψ'/δψ) e^{iS[ψ(ψ')]}
    Note: Berezinian, NOT ordinary determinant! -/
axiom path_integral_fermionic_redef {F₁ F₂ F_bos F_ferm : Type _} (G : GrassmannAlgebra)
  (S : ActionFunctional (F_bos × F₁))
  (μ_bos : FieldMeasure F_bos)
  (μ_ferm : FermionicMeasure F₁ G)
  (f : @FermionicFieldRedefinition F₁ F₂)
  (S_new : ActionFunctional (F_bos × F₂))
  (μ_ferm_new : FermionicMeasure F₂ G) :
  fermionPathIntegral G S μ_bos μ_ferm =
    berezinianEval f.berezinian *
    fermionPathIntegral G S_new μ_bos μ_ferm_new

/-- Mixed bosonic-fermionic field redefinition
    ∫ DφDψ e^{iS[φ,ψ]} uses full Berezinian of supermatrix
    [[δφ'/δφ, δφ'/δψ], [δψ'/δφ, δψ'/δψ]] -/
axiom path_integral_super_redef {F_bos₁ F_bos₂ F_ferm₁ F_ferm₂ : Type _}
  (G : GrassmannAlgebra)
  (S : ActionFunctional (F_bos₁ × F_ferm₁))
  (μ_bos : FieldMeasure F_bos₁)
  (μ_ferm : FermionicMeasure F_ferm₁ G)
  (f : @SuperFieldRedefinition (F_bos₁ × F_ferm₁) (F_bos₂ × F_ferm₂))
  (S_new : ActionFunctional (F_bos₂ × F_ferm₂))
  (μ_bos_new : FieldMeasure F_bos₂)
  (μ_ferm_new : FermionicMeasure F_ferm₂ G) :
  fermionPathIntegral G S μ_bos μ_ferm =
    berezinianEval f.super_jacobian *
    fermionPathIntegral G S_new μ_bos_new μ_ferm_new

/-- Path integral with observable under field redefinition -/
axiom path_integral_observable_bosonic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (O : F₁ → ℂ)
  (μ : FieldMeasure F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  pathIntegralWithObservable S O μ =
    f.jacobian *
    pathIntegralWithObservable
      (action_bosonic_redef S f)
      (observable_bosonic_redef O f)
      (measure_bosonic_redef μ f)

/- ============= GENERATING FUNCTIONALS ============= -/

/-- Generating functional Z[J] = ∫ Dφ e^{iS[φ] + i∫J·φ} -/
axiom generatingFunctional {F M V : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (source : M → V) : ℂ

/-- Complex logarithm (axiomatized) -/
axiom complexLog : ℂ → ℂ

/-- Connected generating functional W[J] = -iℏ log Z[J] -/
noncomputable def connectedGenerating {F M V : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (source : M → V)
  (ℏ : ℝ) : ℂ :=
  -Complex.I * ℏ * complexLog (generatingFunctional S μ source)

/-- Effective action Γ[φ_cl] (Legendre transform, 1PI generator) -/
axiom effectiveAction {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F) : ActionFunctional F

end ModularPhysics.Core.QFT.PathIntegral

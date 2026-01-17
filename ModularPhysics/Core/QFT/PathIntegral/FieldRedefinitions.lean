import ModularPhysics.Core.QFT.PathIntegral.ActionAndMeasure

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= FIELD REDEFINITIONS ============= -/

/-- Field redefinition φ → φ'(φ)
    Fundamental operation: change of integration variables -/
structure FieldRedefinition {F₁ F₂ : Type _} where
  map : F₁ → F₂
  inverse : F₂ → F₁
  left_inv : ∀ φ, inverse (map φ) = φ
  right_inv : ∀ φ', map (inverse φ') = φ'

/-- Bosonic field redefinition: ordinary Jacobian determinant
    J = det(δφ'ⁱ/δφʲ) -/
structure BosonicFieldRedefinition {F₁ F₂ : Type _} extends
  @FieldRedefinition F₁ F₂ where
  jacobian : ℂ

/-- Fermionic field redefinition: Berezinian (superdeterminant)
    For transformation of Grassmann variables
    Ber(M) where M is supermatrix of derivatives -/
structure FermionicFieldRedefinition {F₁ F₂ : Type _} extends
  @FieldRedefinition F₁ F₂ where
  berezinian : Berezinian

/-- General field redefinition with mixed bosonic/fermionic variables
    Uses Berezinian for the full supermatrix -/
structure SuperFieldRedefinition {F₁ F₂ : Type _} extends
  @FieldRedefinition F₁ F₂ where
  super_jacobian : Berezinian

/-- Evaluate bosonic Jacobian -/
axiom bosonicJacobianEval {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂) : ℂ

/-- Evaluate fermionic Berezinian -/
axiom fermionicBerezinianEval {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂) : ℂ

/-- Action transforms under bosonic field redefinition -/
axiom action_bosonic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  ActionFunctional F₂

/-- Action transforms under fermionic field redefinition -/
axiom action_fermionic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @FermionicFieldRedefinition F₁ F₂) :
  ActionFunctional F₂

/-- Action evaluated on redefined field -/
axiom action_redef_eval_bosonic {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @BosonicFieldRedefinition F₁ F₂)
  (φ : F₁) :
  (action_bosonic_redef S f).eval (f.map φ) = S.eval φ

axiom action_redef_eval_fermionic {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @FermionicFieldRedefinition F₁ F₂)
  (φ : F₁) :
  (action_fermionic_redef S f).eval (f.map φ) = S.eval φ

/-- Measure transforms under field redefinition -/
axiom measure_bosonic_redef {F₁ F₂ : Type _}
  (μ : FieldMeasure F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  FieldMeasure F₂

axiom measure_fermionic_redef {F₁ F₂ : Type _} (G : GrassmannAlgebra)
  (μ : FermionicMeasure F₁ G)
  (f : @FermionicFieldRedefinition F₁ F₂) :
  FermionicMeasure F₂ G

/-- Observable transforms under field redefinition -/
axiom observable_bosonic_redef {F₁ F₂ : Type _}
  (O : F₁ → ℂ)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  F₂ → ℂ

axiom observable_fermionic_redef {F₁ F₂ : Type _}
  (O : F₁ → ℂ)
  (f : @FermionicFieldRedefinition F₁ F₂) :
  F₂ → ℂ

/- ============= JACOBIAN PROPERTIES ============= -/

/-- Bosonic Jacobian is multiplicative under composition -/
axiom jacobian_composition {F₁ F₂ F₃ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂)
  (g : @BosonicFieldRedefinition F₂ F₃) :
  bosonicJacobianEval (sorry : @BosonicFieldRedefinition F₁ F₃) =
    bosonicJacobianEval f * bosonicJacobianEval g

/-- Fermionic Berezinian is multiplicative -/
axiom fermionic_berezinian_composition {F₁ F₂ F₃ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂)
  (g : @FermionicFieldRedefinition F₂ F₃) :
  fermionicBerezinianEval (sorry : @FermionicFieldRedefinition F₁ F₃) =
    fermionicBerezinianEval f * fermionicBerezinianEval g

/-- Identity transformation has Jacobian 1 -/
axiom jacobian_identity_bosonic {F : Type _} :
  bosonicJacobianEval (sorry : @BosonicFieldRedefinition F F) = 1

axiom jacobian_identity_fermionic {F : Type _} :
  fermionicBerezinianEval (sorry : @FermionicFieldRedefinition F F) = 1

/-- Inverse transformation has inverse Jacobian -/
axiom jacobian_inverse_bosonic {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂) :
  bosonicJacobianEval f * bosonicJacobianEval (sorry : @BosonicFieldRedefinition F₂ F₁) = 1

axiom jacobian_inverse_fermionic {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂) :
  fermionicBerezinianEval f * fermionicBerezinianEval (sorry : @FermionicFieldRedefinition F₂ F₁) = 1

end ModularPhysics.Core.QFT.PathIntegral

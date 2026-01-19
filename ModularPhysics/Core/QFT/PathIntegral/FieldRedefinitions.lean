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
def bosonicJacobianEval {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂) : ℂ := f.jacobian

/-- Evaluate fermionic Berezinian -/
noncomputable def fermionicBerezinianEval {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂) : ℂ := berezinianEval f.berezinian

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

/- ============= COMPOSITION OF FIELD REDEFINITIONS ============= -/

/-- Compose two bosonic field redefinitions -/
def composeBosonic {F₁ F₂ F₃ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂)
  (g : @BosonicFieldRedefinition F₂ F₃) : @BosonicFieldRedefinition F₁ F₃ where
  map := g.map ∘ f.map
  inverse := f.inverse ∘ g.inverse
  left_inv := fun φ => by simp [f.left_inv, g.left_inv]
  right_inv := fun φ' => by simp [f.right_inv, g.right_inv]
  jacobian := f.jacobian * g.jacobian

/-- Compose two fermionic field redefinitions -/
def composeFermionic {F₁ F₂ F₃ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂)
  (g : @FermionicFieldRedefinition F₂ F₃) : @FermionicFieldRedefinition F₁ F₃ where
  map := g.map ∘ f.map
  inverse := f.inverse ∘ g.inverse
  left_inv := fun φ => by simp [f.left_inv, g.left_inv]
  right_inv := fun φ' => by simp [f.right_inv, g.right_inv]
  berezinian := berezinianCompose f.berezinian g.berezinian

/-- Identity bosonic field redefinition -/
def idBosonic (F : Type _) : @BosonicFieldRedefinition F F where
  map := id
  inverse := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  jacobian := 1

/-- Identity fermionic field redefinition -/
def idFermionic (F : Type _) : @FermionicFieldRedefinition F F where
  map := id
  inverse := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  berezinian := berezinianId

/-- Inverse of bosonic field redefinition -/
noncomputable def inverseBosonic {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂)
  (h : f.jacobian ≠ 0) : @BosonicFieldRedefinition F₂ F₁ where
  map := f.inverse
  inverse := f.map
  left_inv := f.right_inv
  right_inv := f.left_inv
  jacobian := f.jacobian⁻¹

/-- Inverse of fermionic field redefinition -/
noncomputable def inverseFermionic {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂)
  (h : f.berezinian.val ≠ 0) : @FermionicFieldRedefinition F₂ F₁ where
  map := f.inverse
  inverse := f.map
  left_inv := f.right_inv
  right_inv := f.left_inv
  berezinian := berezinianInv f.berezinian

/- ============= JACOBIAN PROPERTIES ============= -/

/-- Bosonic Jacobian is multiplicative under composition -/
theorem jacobian_composition {F₁ F₂ F₃ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂)
  (g : @BosonicFieldRedefinition F₂ F₃) :
  bosonicJacobianEval (composeBosonic f g) =
    bosonicJacobianEval f * bosonicJacobianEval g := rfl

/-- Fermionic Berezinian is multiplicative -/
theorem fermionic_berezinian_composition {F₁ F₂ F₃ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂)
  (g : @FermionicFieldRedefinition F₂ F₃) :
  fermionicBerezinianEval (composeFermionic f g) =
    fermionicBerezinianEval f * fermionicBerezinianEval g := rfl

/-- Identity transformation has Jacobian 1 -/
theorem jacobian_identity_bosonic {F : Type _} :
  bosonicJacobianEval (idBosonic F) = 1 := rfl

theorem jacobian_identity_fermionic {F : Type _} :
  fermionicBerezinianEval (idFermionic F) = 1 := rfl

/-- Inverse transformation has inverse Jacobian -/
theorem jacobian_inverse_bosonic {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂)
  (h : f.jacobian ≠ 0) :
  bosonicJacobianEval f * bosonicJacobianEval (inverseBosonic f h) = 1 := by
  simp only [bosonicJacobianEval, inverseBosonic]
  exact mul_inv_cancel₀ h

theorem jacobian_inverse_fermionic {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂)
  (h : f.berezinian.val ≠ 0) :
  fermionicBerezinianEval f * fermionicBerezinianEval (inverseFermionic f h) = 1 :=
  berezinian_inverse f.berezinian h

end ModularPhysics.Core.QFT.PathIntegral

-- ModularPhysics/Core/QFT/PathIntegral/FieldRedefinitions.lean
-- Field redefinitions (change of integration variables in the path integral)
--
-- A field redefinition φ → φ'(φ) is a diffeomorphism of field space.
-- Under this change of variables, the path integral transforms as:
--   ∫ Dφ e^{iS[φ]} = ∫ Dφ' |J| e^{iS[φ(φ')]}
-- where J is the Jacobian (or Berezinian for fermions).
import ModularPhysics.Core.QFT.PathIntegral.ActionAndMeasure

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= FIELD REDEFINITIONS ============= -/

/-- Field redefinition φ → φ'(φ): a bijection of field space.
    This is the fundamental operation of changing integration variables. -/
structure FieldRedefinition (F₁ F₂ : Type*) where
  /-- Forward map: φ ↦ φ' -/
  map : F₁ → F₂
  /-- Inverse map: φ' ↦ φ -/
  inverse : F₂ → F₁
  /-- Left inverse property -/
  left_inv : ∀ φ, inverse (map φ) = φ
  /-- Right inverse property -/
  right_inv : ∀ φ', map (inverse φ') = φ'

/-- Bosonic field redefinition: ordinary Jacobian determinant.
    J = det(δφ'ⁱ/δφʲ) -/
structure BosonicFieldRedefinition (F₁ F₂ : Type*) extends
  FieldRedefinition F₁ F₂ where
  /-- Jacobian determinant of the transformation -/
  jacobian : ℂ

/-- Fermionic field redefinition: Berezinian (superdeterminant).
    For transformation of Grassmann variables. -/
structure FermionicFieldRedefinition (F₁ F₂ : Type*) extends
  FieldRedefinition F₁ F₂ where
  /-- Berezinian of the transformation -/
  berezinian : Berezinian

/-- General field redefinition with mixed bosonic/fermionic variables.
    Uses the full Berezinian for the supermatrix of derivatives. -/
structure SuperFieldRedefinition (F₁ F₂ : Type*) extends
  FieldRedefinition F₁ F₂ where
  /-- Berezinian of the full super-Jacobian -/
  super_jacobian : Berezinian

/- ============= PULLBACK OF ACTION AND MEASURE ============= -/

/-- Action transforms under bosonic field redefinition by pullback:
    S'[φ'] = S[f⁻¹(φ')] -/
def action_bosonic_redef {F₁ F₂ : Type*}
    (S : ActionFunctional F₁) (f : BosonicFieldRedefinition F₁ F₂) :
    ActionFunctional F₂ where
  eval := S.eval ∘ f.inverse

/-- Action transforms under fermionic field redefinition by pullback -/
def action_fermionic_redef {F₁ F₂ : Type*}
    (S : ActionFunctional F₁) (f : FermionicFieldRedefinition F₁ F₂) :
    ActionFunctional F₂ where
  eval := S.eval ∘ f.inverse

/-- Measure transforms under bosonic field redefinition.
    ∫ Dφ f(φ) = ∫ Dφ' |J|⁻¹ f(g(φ')) where g = f⁻¹ -/
def measure_bosonic_redef {F₁ F₂ : Type*}
    (μ : FieldMeasure F₁) (f : BosonicFieldRedefinition F₁ F₂) :
    FieldMeasure F₂ where
  integrate := fun obs => μ.integrate (obs ∘ f.map)

/-- Observable transforms under bosonic field redefinition by pullback:
    O'(φ') = O(f⁻¹(φ')) -/
def observable_bosonic_redef {F₁ F₂ : Type*}
    (O : F₁ → ℂ) (f : BosonicFieldRedefinition F₁ F₂) : F₂ → ℂ :=
  O ∘ f.inverse

/-- Observable transforms under fermionic field redefinition by pullback -/
def observable_fermionic_redef {F₁ F₂ : Type*}
    (O : F₁ → ℂ) (f : FermionicFieldRedefinition F₁ F₂) : F₂ → ℂ :=
  O ∘ f.inverse

/-- Action evaluated on redefined field returns original value -/
theorem action_redef_eval_bosonic {F₁ F₂ : Type*}
    (S : ActionFunctional F₁) (f : BosonicFieldRedefinition F₁ F₂)
    (φ : F₁) :
    (action_bosonic_redef S f).eval (f.map φ) = S.eval φ := by
  simp [action_bosonic_redef, Function.comp, f.left_inv]

/-- Action evaluated on redefined field returns original value (fermionic) -/
theorem action_redef_eval_fermionic {F₁ F₂ : Type*}
    (S : ActionFunctional F₁) (f : FermionicFieldRedefinition F₁ F₂)
    (φ : F₁) :
    (action_fermionic_redef S f).eval (f.map φ) = S.eval φ := by
  simp [action_fermionic_redef, Function.comp, f.left_inv]

/- ============= JACOBIAN EVALUATION ============= -/

/-- Evaluate bosonic Jacobian -/
def bosonicJacobianEval {F₁ F₂ : Type*}
    (f : BosonicFieldRedefinition F₁ F₂) : ℂ := f.jacobian

/-- Evaluate fermionic Berezinian -/
noncomputable def fermionicBerezinianEval {F₁ F₂ : Type*}
    (f : FermionicFieldRedefinition F₁ F₂) : ℂ := berezinianEval f.berezinian

/- ============= COMPOSITION OF FIELD REDEFINITIONS ============= -/

/-- Compose two bosonic field redefinitions -/
def composeBosonic {F₁ F₂ F₃ : Type*}
    (f : BosonicFieldRedefinition F₁ F₂)
    (g : BosonicFieldRedefinition F₂ F₃) : BosonicFieldRedefinition F₁ F₃ where
  map := g.map ∘ f.map
  inverse := f.inverse ∘ g.inverse
  left_inv := fun φ => by simp [f.left_inv, g.left_inv]
  right_inv := fun φ' => by simp [f.right_inv, g.right_inv]
  jacobian := f.jacobian * g.jacobian

/-- Compose two fermionic field redefinitions -/
def composeFermionic {F₁ F₂ F₃ : Type*}
    (f : FermionicFieldRedefinition F₁ F₂)
    (g : FermionicFieldRedefinition F₂ F₃) : FermionicFieldRedefinition F₁ F₃ where
  map := g.map ∘ f.map
  inverse := f.inverse ∘ g.inverse
  left_inv := fun φ => by simp [f.left_inv, g.left_inv]
  right_inv := fun φ' => by simp [f.right_inv, g.right_inv]
  berezinian := berezinianCompose f.berezinian g.berezinian

/-- Identity bosonic field redefinition -/
def idBosonic (F : Type*) : BosonicFieldRedefinition F F where
  map := id
  inverse := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  jacobian := 1

/-- Identity fermionic field redefinition -/
def idFermionic (F : Type*) : FermionicFieldRedefinition F F where
  map := id
  inverse := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  berezinian := berezinianId

/-- Inverse of bosonic field redefinition -/
noncomputable def inverseBosonic {F₁ F₂ : Type*}
    (f : BosonicFieldRedefinition F₁ F₂) (h : f.jacobian ≠ 0) :
    BosonicFieldRedefinition F₂ F₁ where
  map := f.inverse
  inverse := f.map
  left_inv := f.right_inv
  right_inv := f.left_inv
  jacobian := f.jacobian⁻¹

/-- Inverse of fermionic field redefinition -/
noncomputable def inverseFermionic {F₁ F₂ : Type*}
    (f : FermionicFieldRedefinition F₁ F₂) (h : f.berezinian.val ≠ 0) :
    FermionicFieldRedefinition F₂ F₁ where
  map := f.inverse
  inverse := f.map
  left_inv := f.right_inv
  right_inv := f.left_inv
  berezinian := berezinianInv f.berezinian

/- ============= JACOBIAN PROPERTIES ============= -/

/-- Bosonic Jacobian is multiplicative under composition -/
theorem jacobian_composition {F₁ F₂ F₃ : Type*}
    (f : BosonicFieldRedefinition F₁ F₂) (g : BosonicFieldRedefinition F₂ F₃) :
    bosonicJacobianEval (composeBosonic f g) =
    bosonicJacobianEval f * bosonicJacobianEval g := rfl

/-- Fermionic Berezinian is multiplicative -/
theorem fermionic_berezinian_composition {F₁ F₂ F₃ : Type*}
    (f : FermionicFieldRedefinition F₁ F₂) (g : FermionicFieldRedefinition F₂ F₃) :
    fermionicBerezinianEval (composeFermionic f g) =
    fermionicBerezinianEval f * fermionicBerezinianEval g := rfl

/-- Identity transformation has Jacobian 1 -/
theorem jacobian_identity_bosonic {F : Type*} :
    bosonicJacobianEval (idBosonic F) = 1 := rfl

theorem jacobian_identity_fermionic {F : Type*} :
    fermionicBerezinianEval (idFermionic F) = 1 := rfl

/-- Inverse transformation has inverse Jacobian -/
theorem jacobian_inverse_bosonic {F₁ F₂ : Type*}
    (f : BosonicFieldRedefinition F₁ F₂) (h : f.jacobian ≠ 0) :
    bosonicJacobianEval f * bosonicJacobianEval (inverseBosonic f h) = 1 := by
  simp only [bosonicJacobianEval, inverseBosonic]
  exact mul_inv_cancel₀ h

theorem jacobian_inverse_fermionic {F₁ F₂ : Type*}
    (f : FermionicFieldRedefinition F₁ F₂) (h : f.berezinian.val ≠ 0) :
    fermionicBerezinianEval f * fermionicBerezinianEval (inverseFermionic f h) = 1 :=
  berezinian_inverse f.berezinian h

end ModularPhysics.Core.QFT.PathIntegral

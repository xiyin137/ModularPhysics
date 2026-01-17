import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.PathIntegral

open SpaceTime

set_option autoImplicit false
set_option linter.unusedVariables false

/- ============= FIELD CONFIGURATIONS ============= -/

/-- Space of field configurations (NOT necessarily a vector space)
    Examples:
    - Linear: φ : M → ℝ (vector space)
    - Nonlinear σ-model: φ : M → S² (maps to sphere)
    - Gauge theory: A : M → Lie(G) with gauge equivalence
    - Fermions: ψ with anticommuting values (supermanifold structure) -/
axiom FieldConfig (M : Type _) (target : Type _) : Type _

/-- Pointwise evaluation of field configuration -/
axiom evalField {M target : Type _} : FieldConfig M target → M → target

/-- Field space for linear theory (vector space structure) -/
class LinearFieldSpace (M : Type _) (V : Type _) extends
  AddCommGroup (FieldConfig M V) where
  smul : ℝ → FieldConfig M V → FieldConfig M V
  smul_add : ∀ (a : ℝ) (φ ψ : FieldConfig M V),
    smul a (φ + ψ) = smul a φ + smul a ψ

/-- Field space for nonlinear σ-model (target manifold structure) -/
structure NonlinearSigmaModel (M : Type _) (target : Type _) where
  /-- Target space is a Riemannian manifold -/
  target_manifold : Type _
  metric : target → target → ℝ
  /-- Field configurations are smooth maps -/
  field_space : Type _
  smooth : field_space → Prop

/-- Gauge field with gauge redundancy -/
structure GaugeFieldSpace (M : Type _) (G : Type _) where
  /-- Lie algebra-valued connection -/
  connection_space : Type _
  /-- Gauge transformations -/
  gauge_group : Type _
  gauge_action : gauge_group → connection_space → connection_space
  /-- Physical configurations modulo gauge -/
  physical_space : Type _

/-- Fermionic field configurations
    Mathematical reality: configuration space is a supermanifold
    Practical note: for ordinary QFT, super vector space structure suffices -/
axiom FermionFieldConfig (M : Type _) : Type _

/-- General field configuration space (no a priori structure) -/
axiom FieldSpace (M : Type _) : Type _

end ModularPhysics.Core.QFT.PathIntegral

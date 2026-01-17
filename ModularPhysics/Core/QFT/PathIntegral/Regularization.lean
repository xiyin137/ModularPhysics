import ModularPhysics.Core.QFT.PathIntegral.PathIntegrals

namespace ModularPhysics.Core.QFT.PathIntegral

set_option linter.unusedVariables false

/- ============= REGULARIZATION ============= -/

/-- UV cutoff -/
structure UVCutoff where
  scale : ℝ
  positive : scale > 0

/-- Regularized path integral -/
axiom regularizedPathIntegral {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (Λ : UVCutoff) : ℂ

/-- Dimensional regularization -/
axiom dimensionalRegularization {F : Type _}
  (S : ActionFunctional F)
  (ε : ℝ) : ℂ

/-- Lattice regularization -/
structure LatticeRegularization where
  spacing : ℝ
  spacing_positive : spacing > 0

/-- Lattice path integral -/
axiom latticePathIntegral {F : Type _}
  (S : ActionFunctional F)
  (a : LatticeRegularization) : ℂ

/-- Continuum limit requires RG flow of couplings -/
structure ContinuumLimit {F : Type _}
  (S_lattice : LatticeRegularization → ActionFunctional F) where
  bare_couplings : LatticeRegularization → List ℝ
  rg_flow : ∀ (a : LatticeRegularization) (g : List ℝ), List ℝ
  critical_surface : Prop
  limit_exists : Prop

/-- Naive limit with fixed couplings fails -/
axiom naive_continuum_limit_fails {F : Type _}
  (S : ActionFunctional F)
  (g_fixed : List ℝ) : Prop

/-- Pauli-Villars regularization -/
structure PauliVillarsRegularization where
  regulator_masses : List ℝ
  signs : List ℤ
  /-- Signs alternate to cancel divergences -/
  sign_constraint : ∀ i : Fin signs.length, signs[i] = 1 ∨ signs[i] = -1

/-- Zeta function regularization -/
axiom zetaFunctionRegularization {F : Type _}
  (S : ActionFunctional F)
  (s : ℂ) : ℂ

end ModularPhysics.Core.QFT.PathIntegral

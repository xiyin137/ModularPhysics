import ModularPhysics.Core.ClassicalFieldTheory.EulerLagrange
import ModularPhysics.Core.ClassicalFieldTheory.EnergyMomentum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Structure for scalar field theory -/
structure ScalarFieldTheory (sfo : ScalarFieldOperators) (at : ActionTheory ℝ)
    (eom : EquationsOfMotion ℝ at) where
  /-- Free scalar field Lagrangian: L = (1/2)∂_μφ ∂^μφ - (1/2)m²φ² -/
  freeScalarLagrangian : ℝ → ScalarField → ScalarField
  /-- φ⁴ interaction Lagrangian: L = L_free - (λ/4!)φ⁴ -/
  phi4Lagrangian : ℝ → ℝ → ScalarField → ScalarField
  /-- Sine-Gordon Lagrangian: L = (1/2)∂_μφ ∂^μφ + (m²/β²)cos(βφ) -/
  sineGordonLagrangian : ℝ → ℝ → ScalarField → ScalarField
  /-- Soliton solution -/
  solitonSolution : ℝ → ScalarField
  /-- Free scalar field satisfies Klein-Gordon equation -/
  free_scalar_satisfies_kg : ∀ (phi : ScalarField) (m : ℝ),
    eom.eulerLagrange phi →
    ∀ x, sfo.dalembertian phi x + m^2 * phi x = 0
  /-- φ⁴ equation of motion: (□ + m²)φ + (λ/6)φ³ = 0 -/
  phi4_equation : ∀ (phi : ScalarField) (m lambda : ℝ),
    eom.eulerLagrange phi →
    ∀ x, sfo.dalembertian phi x + m^2 * phi x + (lambda/6) * (phi x)^3 = 0

/-- Klein-Gordon equation: (□ + m²)φ = 0 -/
def kleinGordonEquation (sfo : ScalarFieldOperators) (phi : ScalarField) (m : ℝ) : Prop :=
  ∀ x, sfo.dalembertian phi x + m^2 * phi x = 0

/-- Sine-Gordon equation: □φ - (m²/β)sin(βφ) = 0 -/
def sineGordonEquation (sfo : ScalarFieldOperators) (phi : ScalarField) (m beta : ℝ) : Prop :=
  ∀ x, sfo.dalembertian phi x - (m^2 / beta) * Real.sin (beta * phi x) = 0

/-- Structure for charged scalar field theory (complex) -/
structure ChargedScalarTheory (at : ActionTheory ℂ)
    (eom : EquationsOfMotion ℂ at)
    (fd : FieldDerivatives ℂ) where
  /-- Charged scalar field Lagrangian: L = ∂_μφ* ∂^μφ - m²|φ|² -/
  chargedScalarLagrangian : ℝ → ComplexScalarField → ScalarField
  /-- Global U(1) symmetry: φ → e^(iα)φ -/
  u1Symmetry : ℝ → ComplexScalarField → ComplexScalarField
  /-- Noether current from U(1) symmetry: j^μ = i(φ* ∂^μφ - φ ∂^μφ*) -/
  u1Current : ComplexScalarField → VectorField
  /-- U(1) charge conservation: ∂_μ j^μ = 0 -/
  u1_charge_conservation : ∀ (phi : ComplexScalarField)
      (h : eom.eulerLagrange phi)
      (x : SpaceTimePoint),
    ∑ μ, fd.partialDerivative (fun y => u1Current phi y μ) μ x = 0

end ModularPhysics.Core.ClassicalFieldTheory

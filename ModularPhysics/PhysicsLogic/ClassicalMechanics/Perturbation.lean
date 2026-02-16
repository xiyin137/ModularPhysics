import ModularPhysics.PhysicsLogic.ClassicalMechanics.Integrable

namespace ModularPhysics.Core.ClassicalMechanics

variable {n : ℕ}

/-- Perturbed Hamiltonian H = H₀ + εH₁ -/
noncomputable def perturbedHamiltonian
  (H₀ : PhaseSpace n → ℝ)
  (H₁ : PhaseSpace n → ℝ)
  (ε : ℝ) : PhaseSpace n → ℝ :=
  fun x => H₀ x + ε * H₁ x

/-- Structure for perturbation theory -/
structure PerturbationTheory (n : ℕ) where
  /-- The underlying integrable system theory -/
  intTheory : IntegrableSystemTheory n
  /-- Canonical perturbation theory to given order -/
  canonicalPerturbationTheory : (PhaseSpace n → ℝ) → (PhaseSpace n → ℝ) → ℕ → PhaseSpace n → ℝ

end ModularPhysics.Core.ClassicalMechanics

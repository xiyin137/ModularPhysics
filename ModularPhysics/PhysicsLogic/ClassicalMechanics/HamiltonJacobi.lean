import ModularPhysics.PhysicsLogic.ClassicalMechanics.Hamiltonian
import ModularPhysics.PhysicsLogic.ClassicalMechanics.CanonicalTransforms
import ModularPhysics.PhysicsLogic.ClassicalMechanics.Integrable

namespace ModularPhysics.Core.ClassicalMechanics

variable {n : ℕ}

/-- Hamilton's principal function S(q, t) -/
abbrev HamiltonPrincipalFunction (n : ℕ) :=
  GeneralizedCoordinates n → ℝ → ℝ

/-- Hamilton's characteristic function W(q, α) (time-independent) -/
abbrev HamiltonCharacteristicFunction (n : ℕ) :=
  GeneralizedCoordinates n → (Fin n → ℝ) → ℝ

/-- Structure for Hamilton-Jacobi theory -/
structure HamiltonJacobiTheory (n : ℕ) where
  /-- The underlying Lagrangian-Hamiltonian system -/
  lhSystem : LagrangianHamiltonianSystem n
  /-- The integrable system theory -/
  intTheory : IntegrableSystemTheory n
  /-- Partial derivative of S with respect to coordinate -/
  partialS_q : HamiltonPrincipalFunction n → GeneralizedCoordinates n → ℝ → Fin n → ℝ
  /-- Solution of HJ equation gives canonical transformation -/
  hj_generates_canonical_transform :
    ∀ (S : HamiltonPrincipalFunction n)
      (h : ∀ q t, deriv (S q) t + lhSystem.H q (fun i => partialS_q S q t i) t = 0),
    ∃ (_ : CanonicalTransformation n lhSystem.toHamiltonianSystem), True
  /-- Hamilton-Jacobi method solves for trajectories -/
  hj_gives_trajectories :
    ∀ (S : HamiltonPrincipalFunction n)
      (h : ∀ q t, deriv (S q) t + lhSystem.H q (fun i => partialS_q S q t i) t = 0)
      (q₀ : GeneralizedCoordinates n),
    ∃ (q : Trajectory n), q 0 = q₀ ∧ satisfiesAllEulerLagrange lhSystem.toLagrangianSystem q
  /-- Separation of variables in HJ equation -/
  hj_separation_of_variables :
    ∀ (W : HamiltonCharacteristicFunction n)
      (h_separable : ∃ (Wᵢ : Fin n → ℝ → (Fin n → ℝ) → ℝ),
                       ∀ (q : GeneralizedCoordinates n) (alpha : Fin n → ℝ),
                         W q alpha = ∑ i, Wᵢ i (q i) alpha),
    ∃ E, ∀ (q : GeneralizedCoordinates n) (alpha : Fin n → ℝ),
      lhSystem.H q (fun i => partialS_q (fun q' _ => W q' alpha) q 0 i) 0 = E
  /-- Connection to action variables -/
  hj_gives_action_variables :
    ∀ (W : HamiltonCharacteristicFunction n) (E : ℝ)
      (h : ∀ (q : GeneralizedCoordinates n) (alpha : Fin n → ℝ),
             lhSystem.H q (fun i => partialS_q (fun q' _ => W q' alpha) q 0 i) 0 = E)
      (i : Fin n) (γ : PhaseSpaceTrajectory n),
    ∃ (integral : ℝ), intTheory.actionVariable i γ = integral

/-- Hamilton-Jacobi equation: ∂S/∂t + H(q, ∂S/∂q, t) = 0 -/
def satisfiesHamiltonJacobi
  (theory : HamiltonJacobiTheory n)
  (S : HamiltonPrincipalFunction n) : Prop :=
  ∀ q t, deriv (S q) t + theory.lhSystem.H q (fun i => theory.partialS_q S q t i) t = 0

/-- Time-independent Hamilton-Jacobi: H(q, ∂W/∂q) = E -/
def satisfiesTimeIndependentHJ
  (theory : HamiltonJacobiTheory n)
  (W : HamiltonCharacteristicFunction n)
  (E : ℝ) : Prop :=
  ∀ (q : GeneralizedCoordinates n) (alpha : Fin n → ℝ),
    theory.lhSystem.H q (fun i => theory.partialS_q (fun q' _ => W q' alpha) q 0 i) 0 = E

end ModularPhysics.Core.ClassicalMechanics

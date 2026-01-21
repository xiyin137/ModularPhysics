import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

namespace ModularPhysics.Core.Quantum

set_option autoImplicit false

/-- A quantum state space (abstract Hilbert space) -/
class QuantumStateSpace (H : Type _) extends
  NormedAddCommGroup H,
  InnerProductSpace ℂ H,
  CompleteSpace H

/-- 2-dimensional complex Hilbert space (qubit) -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- n-dimensional complex Hilbert space -/
abbrev FiniteDimQuantum (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Qubit is a quantum state space -/
noncomputable instance : QuantumStateSpace Qubit := {}

/-- Finite dimensional systems are quantum state spaces -/
noncomputable instance (n : ℕ) : QuantumStateSpace (FiniteDimQuantum n) := {}

/-- Pure state (normalized vector) -/
structure PureState (H : Type _) [QuantumStateSpace H] where
  vec : H
  normalized : ‖vec‖ = 1

/-- Inner product (probability amplitude) -/
noncomputable def innerProduct {H : Type _} [QuantumStateSpace H] (ψ φ : H) : ℂ :=
  @inner ℂ H _ ψ φ

/-- Superposition principle -/
noncomputable def superposition {H : Type _} [QuantumStateSpace H]
    (α β : ℂ) (ψ φ : H) : H :=
  α • ψ + β • φ

/-- A computational basis for a qubit consists of two orthonormal vectors
    that span the space. -/
structure QubitBasis where
  /-- The |0⟩ basis state -/
  ket0 : Qubit
  /-- The |1⟩ basis state -/
  ket1 : Qubit
  /-- |0⟩ is normalized -/
  ket0_normalized : ‖ket0‖ = 1
  /-- |1⟩ is normalized -/
  ket1_normalized : ‖ket1‖ = 1
  /-- Orthogonality: ⟨0|1⟩ = 0 -/
  orthogonal : @inner ℂ Qubit _ ket0 ket1 = 0
  /-- Completeness: any qubit can be written as a superposition -/
  complete : ∀ (ψ : Qubit), ∃ (α β : ℂ), ψ = superposition α β ket0 ket1

/-- The standard computational basis using the canonical basis vectors -/
noncomputable def standardBasis : QubitBasis where
  ket0 := EuclideanSpace.single 0 1
  ket1 := EuclideanSpace.single 1 1
  ket0_normalized := by simp [EuclideanSpace.norm_single]
  ket1_normalized := by simp [EuclideanSpace.norm_single]
  orthogonal := by
    simp only [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
    simp
  complete := fun ψ => by
    use ψ 0, ψ 1
    ext i
    simp only [superposition]
    fin_cases i <;> simp

namespace QubitBasis

variable (basis : QubitBasis)

/-- Get |0⟩ as a pure state -/
def pureKet0 : PureState Qubit := ⟨basis.ket0, basis.ket0_normalized⟩

/-- Get |1⟩ as a pure state -/
def pureKet1 : PureState Qubit := ⟨basis.ket1, basis.ket1_normalized⟩

/-- Decompose a qubit into basis coefficients -/
noncomputable def decompose (ψ : Qubit) : ℂ × ℂ :=
  (@inner ℂ Qubit _ basis.ket0 ψ, @inner ℂ Qubit _ basis.ket1 ψ)

end QubitBasis

end ModularPhysics.Core.Quantum

import ModularPhysics.PhysicsLogic.Quantum.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ModularPhysics.Core.Quantum

/-- Tensor product of two quantum systems.
    This is kept abstract as the proper tensor product of Hilbert spaces
    requires significant infrastructure. The key property is that it's
    also a quantum state space. -/
structure TensorProductSpace (H₁ H₂ : Type _) [QuantumStateSpace H₁] [QuantumStateSpace H₂] where
  /-- The carrier type of the tensor product -/
  carrier : Type _
  /-- The tensor product has QuantumStateSpace structure -/
  [inst : QuantumStateSpace carrier]
  /-- The tensor product operation -/
  tensor : H₁ → H₂ → carrier
  /-- Tensor product is bilinear in first argument -/
  tensor_add_left : ∀ (ψ₁ ψ₂ : H₁) (φ : H₂), tensor (ψ₁ + ψ₂) φ = tensor ψ₁ φ + tensor ψ₂ φ
  /-- Tensor product is bilinear in second argument -/
  tensor_add_right : ∀ (ψ : H₁) (φ₁ φ₂ : H₂), tensor ψ (φ₁ + φ₂) = tensor ψ φ₁ + tensor ψ φ₂
  /-- Scalar multiplication in first argument -/
  tensor_smul_left : ∀ (a : ℂ) (ψ : H₁) (φ : H₂), tensor (a • ψ) φ = a • tensor ψ φ
  /-- Scalar multiplication in second argument -/
  tensor_smul_right : ∀ (a : ℂ) (ψ : H₁) (φ : H₂), tensor ψ (a • φ) = a • tensor ψ φ

attribute [instance] TensorProductSpace.inst

/-- Abbreviation for the carrier of a tensor product space -/
abbrev TensorProduct {H₁ H₂ : Type _} [QuantumStateSpace H₁] [QuantumStateSpace H₂]
    (T : TensorProductSpace H₁ H₂) : Type _ := T.carrier

/-- Tensor product notation -/
notation:100 ψ " ⊗[" T "] " φ => TensorProductSpace.tensor T ψ φ

/-- For qubits, we use the 4-dimensional space as the tensor product.
    The actual tensor product construction is left abstract. -/
abbrev QubitPair := FiniteDimQuantum 4

/-- QubitPair is a quantum state space -/
noncomputable instance : QuantumStateSpace QubitPair := inferInstance

/-- Abstract tensor product structure for qubits.
    The construction details are left unspecified - this captures only
    the essential algebraic properties. -/
noncomputable def qubitTensorProduct : TensorProductSpace Qubit Qubit where
  carrier := QubitPair
  inst := inferInstance
  tensor := fun ψ φ => (ψ 0 * φ 0) • EuclideanSpace.single 0 1 +
                        (ψ 0 * φ 1) • EuclideanSpace.single 1 1 +
                        (ψ 1 * φ 0) • EuclideanSpace.single 2 1 +
                        (ψ 1 * φ 1) • EuclideanSpace.single 3 1
  tensor_add_left := by
    intros ψ₁ ψ₂ φ
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, add_mul] <;> ring
  tensor_add_right := by
    intros ψ φ₁ φ₂
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, mul_add] <;> ring
  tensor_smul_left := by
    intros a ψ φ
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, smul_eq_mul] <;> ring
  tensor_smul_right := by
    intros a ψ φ
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, smul_eq_mul] <;> ring

/-- A Bell state specification for a given qubit basis and tensor product structure.
    This captures the structure of maximally entangled two-qubit states. -/
structure BellState (basis : QubitBasis) (T : TensorProductSpace Qubit Qubit) where
  /-- The Bell state vector in the tensor product space -/
  state : T.carrier
  /-- Bell state has unit norm -/
  normalized : ‖state‖ = 1
  /-- Bell state has the singlet structure (|01⟩ - |10⟩)/√2 -/
  singlet_form : ∃ (c : ℂ), Complex.normSq c = 1 / 2 ∧
    state = c • ((basis.ket0 ⊗[T] basis.ket1) + ((-1 : ℂ) • (basis.ket1 ⊗[T] basis.ket0)))

/-- Bell state as a pure state -/
def BellState.toPureState {basis : QubitBasis} {T : TensorProductSpace Qubit Qubit}
    (b : BellState basis T) : PureState T.carrier :=
  ⟨b.state, b.normalized⟩

end ModularPhysics.Core.Quantum

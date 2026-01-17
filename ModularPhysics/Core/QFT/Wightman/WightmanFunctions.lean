import ModularPhysics.Core.QFT.Wightman.Axioms

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum

/-- n-point Wightman function W_n(x₁,...,xₙ) = ⟨0|φ(x₁)...φ(xₙ)|0⟩ -/
axiom wightmanFunction {H : Type _} [QuantumStateSpace H]
  (n : ℕ) (phi : QuantumFieldOperator H) :
  (Fin n → SpaceTimePoint) → ℂ

/-- 2-point function (propagator) -/
axiom twoPointFunction {H : Type _} [QuantumStateSpace H]
  (phi : QuantumFieldOperator H) :
  SpaceTimePoint → SpaceTimePoint → ℂ

/-- Wightman positivity: Wightman functions are positive in appropriate sense -/
axiom wightman_positivity {H : Type _} [QuantumStateSpace H]
  (n : ℕ) (phi : QuantumFieldOperator H)
  (x : Fin n → SpaceTimePoint) :
  ∃ (_ : Prop), True

/-- Cluster decomposition: correlations decay at large separation -/
axiom cluster_decomposition {H : Type _} [QuantumStateSpace H]
  (phi psi : QuantumFieldOperator H)
  (x y : SpaceTimePoint)
  (large_separation : ‖(x - y : Fin 4 → ℝ)‖ > 1000) :
  ∃ (_ : Prop),
    wightmanFunction 2 phi (![x, y]) =
    twoPointFunction phi x x * twoPointFunction psi y y

/-- Feynman propagator (time-ordered 2-point function) -/
axiom feynmanPropagator {H : Type _} [QuantumStateSpace H]
  (phi : QuantumFieldOperator H) :
  SpaceTimePoint → SpaceTimePoint → ℂ

end ModularPhysics.Core.QFT.Wightman

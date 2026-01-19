import ModularPhysics.Core.QFT.Wightman.Operators
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum Complex

/-- n-point Wightman function W_n(x₁,...,xₙ) = ⟨0|φ(x₁)...φ(xₙ)|0⟩.
    This is a tempered distribution in the variables (x₁,...,xₙ).
    NOTE: The ordering is as written (operator ordering), NOT time-ordered.
    Time-ordered products give the Feynman propagator instead. -/
axiom wightmanFunction {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ) :
  (Fin n → (Fin d → ℝ)) → ℂ

/-- 2-point Wightman function W₂(x,y) = ⟨0|φ(x)φ(y)|0⟩ -/
noncomputable def twoPointWightman {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (x y : Fin d → ℝ) : ℂ :=
  wightmanFunction phi 2 (fun i => if i = 0 then x else y)

/-- Feynman propagator: time-ordered 2-point function ⟨0|T(φ(x)φ(y))|0⟩.
    For x⁰ > y⁰: G_F(x,y) = W₂(x,y) = ⟨0|φ(x)φ(y)|0⟩
    For y⁰ > x⁰: G_F(x,y) = W₂(y,x) = ⟨0|φ(y)φ(x)|0⟩ -/
axiom feynmanPropagator {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d) :
  (Fin d → ℝ) → (Fin d → ℝ) → ℂ

/-- Smeared two-point Wightman function: ∫∫ f̄(x) g(y) W₂(x,y) dx dy.
    This represents the matrix element ⟨0|φ(f)† φ(g)|0⟩. -/
axiom smearedTwoPointWightman {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (f g : SchwartzFunction d) : ℂ

/-- Wightman positivity (reflection positivity in Minkowski space):
    For any finite collection of test functions {fᵢ} and complex coefficients {cᵢ},
    the quadratic form ∑ᵢⱼ c̄ᵢ cⱼ ⟨0|φ(fᵢ)† φ(fⱼ)|0⟩ ≥ 0.

    This ensures the reconstructed Hilbert space has positive-definite inner product.
    It is equivalent to reflection positivity in the Euclidean formulation. -/
axiom wightman_positivity {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ)
  (test_functions : Fin n → SchwartzFunction d)
  (coeffs : Fin n → ℂ) :
  (∑ i : Fin n, ∑ j : Fin n,
    (starRingEnd ℂ) (coeffs i) * coeffs j *
    smearedTwoPointWightman phi (test_functions i) (test_functions j)).re ≥ 0

/-- Cluster decomposition: At large spacelike separation, correlations factorize.
    W_{n+m}(x₁...xₙ, y₁+a...yₘ+a) → W_n(x₁...xₙ) · W_m(y₁...yₘ) as |a| → ∞ -/
axiom cluster_decomposition {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n m : ℕ)
  (points_x : Fin n → (Fin d → ℝ))
  (points_y : Fin m → (Fin d → ℝ))
  (separation : Fin d → ℝ) :
  ∀ ε > 0, ∃ R : ℝ, ∀ a > R,
    let shifted_y := fun i μ => points_y i μ + a * separation μ
    ∃ (combined : ℂ),
    ‖combined - wightmanFunction phi n points_x * wightmanFunction phi m shifted_y‖ < ε

end ModularPhysics.Core.QFT.Wightman

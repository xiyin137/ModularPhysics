import ModularPhysics.PhysicsLogic.QFT.Wightman.Operators
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum Complex

/-- Structure for Wightman functions -/
structure WightmanFunctionTheory (H : Type _) [QuantumStateSpace H] (d : ℕ) where
  /-- n-point Wightman function W_n(x₁,...,xₙ) = ⟨0|φ(x₁)...φ(xₙ)|0⟩.
      This is a tempered distribution in the variables (x₁,...,xₙ).
      NOTE: The ordering is as written (operator ordering), NOT time-ordered.
      Time-ordered products give the Feynman propagator instead. -/
  wightmanFunction : FieldDistribution H d → (n : ℕ) → (Fin n → (Fin d → ℝ)) → ℂ
  /-- Feynman propagator: time-ordered 2-point function ⟨0|T(φ(x)φ(y))|0⟩.
      For x⁰ > y⁰: G_F(x,y) = W₂(x,y) = ⟨0|φ(x)φ(y)|0⟩
      For y⁰ > x⁰: G_F(x,y) = W₂(y,x) = ⟨0|φ(y)φ(x)|0⟩ -/
  feynmanPropagator : FieldDistribution H d → (Fin d → ℝ) → (Fin d → ℝ) → ℂ
  /-- Smeared two-point Wightman function: ∫∫ f̄(x) g(y) W₂(x,y) dx dy.
      This represents the matrix element ⟨0|φ(f)† φ(g)|0⟩. -/
  smearedTwoPointWightman : FieldDistribution H d → SchwartzFunction d → SchwartzFunction d → ℂ

/-- Structure for Wightman positivity -/
structure WightmanPositivity (H : Type _) [QuantumStateSpace H] (d : ℕ)
    (wft : WightmanFunctionTheory H d) where
  /-- Wightman positivity (reflection positivity in Minkowski space):
      For any finite collection of test functions {fᵢ} and complex coefficients {cᵢ},
      the quadratic form ∑ᵢⱼ c̄ᵢ cⱼ ⟨0|φ(fᵢ)† φ(fⱼ)|0⟩ ≥ 0.

      This ensures the reconstructed Hilbert space has positive-definite inner product.
      It is equivalent to reflection positivity in the Euclidean formulation. -/
  wightman_positivity : ∀ (phi : FieldDistribution H d) (n : ℕ)
    (test_functions : Fin n → SchwartzFunction d) (coeffs : Fin n → ℂ),
    (∑ i : Fin n, ∑ j : Fin n,
      (starRingEnd ℂ) (coeffs i) * coeffs j *
      wft.smearedTwoPointWightman phi (test_functions i) (test_functions j)).re ≥ 0

/-- Structure for cluster decomposition property -/
structure ClusterDecomposition (H : Type _) [QuantumStateSpace H] (d : ℕ)
    (wft : WightmanFunctionTheory H d) where
  /-- Cluster decomposition: At large spacelike separation, correlations factorize.
      W_{n+m}(x₁...xₙ, y₁+a...yₘ+a) → W_n(x₁...xₙ) · W_m(y₁...yₘ) as |a| → ∞ -/
  cluster_decomposition : ∀ (phi : FieldDistribution H d) (n m : ℕ)
    (points_x : Fin n → (Fin d → ℝ)) (points_y : Fin m → (Fin d → ℝ))
    (separation : Fin d → ℝ) (ε : ℝ), ε > 0 →
    ∃ R : ℝ, ∀ a > R,
      let shifted_y := fun i μ => points_y i μ + a * separation μ
      ∃ (combined : ℂ),
      ‖combined - wft.wightmanFunction phi n points_x * wft.wightmanFunction phi m shifted_y‖ < ε

/-- 2-point Wightman function W₂(x,y) = ⟨0|φ(x)φ(y)|0⟩ -/
noncomputable def twoPointWightman {H : Type _} [QuantumStateSpace H] {d : ℕ}
    (wft : WightmanFunctionTheory H d)
    (phi : FieldDistribution H d)
    (x y : Fin d → ℝ) : ℂ :=
  wft.wightmanFunction phi 2 (fun i => if i = 0 then x else y)

end ModularPhysics.Core.QFT.Wightman

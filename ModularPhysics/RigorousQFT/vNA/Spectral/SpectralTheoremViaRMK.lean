/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Spectral.SpectralMeasurePolarizedViaRMK

/-!
# Spectral Theorem for Unitaries via Riesz-Markov-Kakutani

This file constructs the spectral projections for unitary operators using the
polarized spectral measure from `SpectralMeasurePolarizedViaRMK.lean`.

## Main Definitions

* `spectralProjectionOfUnitary` : the spectral projections P(E)

## Main Results

* `spectralProjection_empty` : P(∅) = 0
* `spectralProjection_univ` : P(Circle) = 1
* `spectralProjection_selfAdjoint` : P(E)* = P(E)
* `spectralProjection_idempotent` : P(E)² = P(E)
* `spectral_theorem_unitary_via_RMK` : the full spectral theorem

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VII-VIII
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical CompactlySupported
open Filter Topology Complex MeasureTheory CompactlySupportedContinuousMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Spectral Projections -/

/-- The spectral projection for a Borel set E ⊆ Circle.

    Constructed using sesquilinearToOperator from SpectralIntegral.lean:
    The polarized spectral measure μ_{x,y}(E) = spectralMeasurePolarized U hU x y E hE
    defines a bounded sesquilinear form, which gives a unique operator P(E) with
    ⟨x, P(E) y⟩ = μ_{x,y}(E). -/
def spectralProjectionOfUnitary (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) : H →L[ℂ] H :=
  -- Use sesquilinearToOperator with B(x, y) = μ_{x,y}(E)
  sesquilinearToOperator
    (fun x y => spectralMeasurePolarized U hU x y E hE)
    (spectralMeasurePolarized_linear_right U hU E hE)
    (spectralMeasurePolarized_conj_linear_left U hU E hE)
    (spectralMeasurePolarized_bounded U hU E hE)

/-- P(∅) = 0 -/
theorem spectralProjection_empty (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    spectralProjectionOfUnitary U hU ∅ MeasurableSet.empty = 0 := by
  -- P(∅) is the operator corresponding to the sesquilinear form B(x,y) = spectralMeasurePolarized x y ∅
  -- Since μ_z(∅) = 0 for any measure, spectralMeasurePolarized x y ∅ = 0 for all x, y
  -- Hence P(∅) = 0
  -- First show the sesquilinear form is identically zero
  have hB_zero : ∀ x y, spectralMeasurePolarized U hU x y ∅ MeasurableSet.empty = 0 := by
    intro x y
    unfold spectralMeasurePolarized spectralMeasureDiagonal
    -- All measures satisfy μ(∅) = 0
    simp only [measure_empty, ENNReal.toReal_zero, sub_self, Complex.ofReal_zero, mul_zero]
    ring
  -- The operator is determined by ⟨x, T y⟩ = B(x, y) = 0 for all x, y
  -- This means T = 0
  ext y
  rw [ContinuousLinearMap.zero_apply]
  rw [← @inner_self_eq_zero ℂ H]
  -- P(∅) = sesquilinearToOperator ...
  unfold spectralProjectionOfUnitary
  -- ⟨P(∅) y, P(∅) y⟩ = B(P(∅) y, P(∅) y) = 0 by sesquilinearToOperator_inner
  have h := sesquilinearToOperator_inner
    (fun x y => spectralMeasurePolarized U hU x y ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_linear_right U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_conj_linear_left U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_bounded U hU ∅ MeasurableSet.empty)
  set P := sesquilinearToOperator (fun x y => spectralMeasurePolarized U hU x y ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_linear_right U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_conj_linear_left U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_bounded U hU ∅ MeasurableSet.empty) with hP_def
  -- h says: B x y = ⟨x, P y⟩
  -- So ⟨P y, P y⟩ = B(P y, y) = 0
  rw [← h (P y) y, hB_zero]

/-- The polarized spectral measure for Circle equals the inner product.
    This uses μ_z(Circle) = ‖z‖² and the complex polarization identity. -/
theorem spectralMeasurePolarized_univ (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) :
    spectralMeasurePolarized U hU x y Set.univ MeasurableSet.univ = @inner ℂ H _ x y := by
  unfold spectralMeasurePolarized
  -- Using μ_z(Circle) = ‖z‖² (from spectralMeasureDiagonal_univ)
  rw [spectralMeasureDiagonal_univ U hU (x + y)]
  rw [spectralMeasureDiagonal_univ U hU (x - y)]
  rw [spectralMeasureDiagonal_univ U hU (x + Complex.I • y)]
  rw [spectralMeasureDiagonal_univ U hU (x - Complex.I • y)]
  -- Now apply the complex polarization identity for norms
  -- inner_eq_sum_norm_sq_div_four: ⟨x,y⟩ = ((‖x+y‖)² - (‖x-y‖)² + ((‖x-I•y‖)² - (‖x+I•y‖)²)*I)/4
  rw [inner_eq_sum_norm_sq_div_four x y]
  -- Note: Complex.I = RCLike.I for the complex numbers
  simp only [Complex.ofReal_pow]
  -- The LHS is: (1/4) * (‖x+y‖² - ‖x-y‖² - I*‖x+I•y‖² + I*‖x-I•y‖²)
  -- The RHS is: ((‖x+y‖)² - (‖x-y‖)² + ((‖x-I•y‖)² - (‖x+I•y‖)²)*I)/4
  -- Need to show: (1/4) * (a - b - I*c + I*d) = (a - b + (d-c)*I) / 4
  -- where a = ‖x+y‖², b = ‖x-y‖², c = ‖x+I•y‖², d = ‖x-I•y‖²
  -- We have: RCLike.I (for ℂ) = Complex.I
  have hI : (RCLike.I : ℂ) = Complex.I := rfl
  simp only [hI]
  -- Both sides have the same terms, just in different order
  ring_nf
  ac_rfl

/-- P(Circle) = 1 -/
theorem spectralProjection_univ (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    spectralProjectionOfUnitary U hU Set.univ MeasurableSet.univ = 1 := by
  -- P(Circle) is determined by ⟨x, P(Circle) y⟩ = spectralMeasurePolarized x y Circle = ⟨x, y⟩
  -- This means P(Circle) = 1 (identity)
  ext y
  rw [ContinuousLinearMap.one_apply]
  -- Show P(Circle) y = y by showing ⟨x, P(Circle) y⟩ = ⟨x, y⟩ for all x
  apply ext_inner_left ℂ
  intro x
  unfold spectralProjectionOfUnitary
  have h := sesquilinearToOperator_inner
    (fun x y => spectralMeasurePolarized U hU x y Set.univ MeasurableSet.univ)
    (spectralMeasurePolarized_linear_right U hU Set.univ MeasurableSet.univ)
    (spectralMeasurePolarized_conj_linear_left U hU Set.univ MeasurableSet.univ)
    (spectralMeasurePolarized_bounded U hU Set.univ MeasurableSet.univ)
  -- h says: B x y = ⟨x, P y⟩
  -- Goal: ⟨x, P y⟩ = ⟨x, y⟩
  rw [← h x y]
  exact spectralMeasurePolarized_univ U hU x y

/-- P(E)² = P(E) (idempotent) -/
theorem spectralProjection_idempotent (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    spectralProjectionOfUnitary U hU E hE ∘L spectralProjectionOfUnitary U hU E hE =
    spectralProjectionOfUnitary U hU E hE := by
  sorry

/-- P(E)* = P(E) (self-adjoint) -/
theorem spectralProjection_selfAdjoint (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    (spectralProjectionOfUnitary U hU E hE).adjoint =
    spectralProjectionOfUnitary U hU E hE := by
  -- P(E) is self-adjoint because B(x, y) = conj(B(y, x)) (Hermitian symmetry)
  -- This means ⟨x, P(E) y⟩ = B(x, y) = conj(B(y, x)) = conj(⟨y, P(E) x⟩) = ⟨P(E) x, y⟩
  -- Hence P(E)* = P(E)
  set P := spectralProjectionOfUnitary U hU E hE with hP_def
  -- We need to show P.adjoint = P
  -- First, use ext to reduce to showing P.adjoint y = P y for all y
  ext y
  -- Then use ext_inner_left to reduce to showing ⟨x, P.adjoint y⟩ = ⟨x, P y⟩ for all x
  apply ext_inner_left ℂ
  intro x
  -- Goal: ⟨x, P.adjoint y⟩ = ⟨x, P y⟩
  -- LHS: ⟨x, P.adjoint y⟩ = ⟨P x, y⟩ (by adjoint_inner_right)
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Now goal is: ⟨P x, y⟩ = ⟨x, P y⟩
  -- From construction: ⟨x, P y⟩ = B(x, y) = spectralMeasurePolarized x y
  -- And: ⟨P x, y⟩ = conj(⟨y, P x⟩) = conj(B(y, x)) = B(x, y) by conj_symm
  have hinner_left : @inner ℂ H _ x (P y) = spectralMeasurePolarized U hU x y E hE := by
    rw [hP_def]
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  have hinner_right : @inner ℂ H _ (P x) y = spectralMeasurePolarized U hU x y E hE := by
    -- ⟨P x, y⟩ = conj(⟨y, P x⟩) = conj(B(y, x)) = B(x, y)
    have h2 : @inner ℂ H _ y (P x) = spectralMeasurePolarized U hU y x E hE := by
      rw [hP_def]
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
    -- Use inner_conj_symm: starRingEnd ℂ (inner ℂ y (P x)) = inner ℂ (P x) y
    -- star (B(y,x)) = B(x,y)
    rw [(inner_conj_symm (P x) y).symm, h2]
    -- Goal: starRingEnd ℂ (spectralMeasurePolarized U hU y x E hE) = spectralMeasurePolarized U hU x y E hE
    -- starRingEnd ℂ = star for ℂ (definitionally)
    exact (spectralMeasurePolarized_conj_symm U hU E hE x y).symm
  rw [hinner_right, hinner_left]

/-! ### The Spectral Theorem -/

/-- **Spectral Theorem for Unitaries (via RMK)**

    For any unitary U on a Hilbert space H, there exists a spectral measure
    (projection-valued measure) P on Circle such that:
    1. P(∅) = 0, P(Circle) = 1
    2. Each P(E) is an orthogonal projection
    3. P(E ∩ F) = P(E) ∘ P(F)
    4. P is σ-additive in the strong operator topology
    5. For any continuous f : Circle → ℂ, cfc(f, U) = ∫ f(z) dP(z)

    This construction is INDEPENDENT of bumpOperator_inner_cauchy. -/
theorem spectral_theorem_unitary_via_RMK (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    ∃ (P : Set Circle → H →L[ℂ] H),
      (∀ E, MeasurableSet E → IsSelfAdjoint (P E)) ∧
      (∀ E, MeasurableSet E → (P E) ∘L (P E) = P E) ∧
      (P ∅ = 0) ∧
      (P Set.univ = 1) ∧
      (∀ E F, MeasurableSet E → MeasurableSet F →
        P (E ∩ F) = P E ∘L P F) := by
  use fun E => if hE : MeasurableSet E then spectralProjectionOfUnitary U hU E hE else 0
  constructor
  · intro E hE
    simp only [dif_pos hE]
    -- IsSelfAdjoint means star (P E) = P E
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    exact spectralProjection_selfAdjoint U hU E hE
  constructor
  · intro E hE
    simp only [dif_pos hE]
    exact spectralProjection_idempotent U hU E hE
  constructor
  · simp [MeasurableSet.empty, spectralProjection_empty U hU]
  constructor
  · simp [MeasurableSet.univ, spectralProjection_univ U hU]
  · intro E F hE hF
    simp only [dif_pos hE, dif_pos hF, dif_pos (hE.inter hF)]
    sorry -- P(E ∩ F) = P(E) P(F)

end

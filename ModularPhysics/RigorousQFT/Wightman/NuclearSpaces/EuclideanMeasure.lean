/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import ModularPhysics.RigorousQFT.Wightman.NuclearSpaces.BochnerMinlos
import ModularPhysics.RigorousQFT.Wightman.NuclearSpaces.SchwartzNuclear

/-!
# Euclidean Field Theory Measures via Minlos' Theorem

This file connects the nuclear space / Minlos infrastructure to the Osterwalder-Schrader
reconstruction theorem, providing the measure-theoretic foundation for Euclidean QFT.

## Main Definitions

* `FreeFieldQuadraticForm` - The quadratic form ⟨f, (-Δ+m²)⁻¹ f⟩ for a free scalar field.
* `FreeFieldCharacteristic` - C(f) = exp(-½ ⟨f, (-Δ+m²)⁻¹ f⟩), the free field
  characteristic functional.
* `euclideanMeasure` - The Gaussian probability measure on S'(ℝᵈ) for the free field.
* `SchwingerFromMeasure` - Schwinger functions as moments of the Euclidean measure.

## Mathematical Background

### The Free Scalar Field Measure

For a free scalar field of mass m > 0 in d Euclidean dimensions, the **Euclidean
measure** is a Gaussian probability measure μ on the space of tempered distributions
S'(ℝᵈ). It is uniquely characterized by its characteristic functional:

  C(f) = ∫_{S'} exp(i φ(f)) dμ(φ) = exp(-½ ⟨f, (-Δ + m²)⁻¹ f⟩_{L²})

where:
- f ∈ S(ℝᵈ) is a Schwartz test function
- φ ∈ S'(ℝᵈ) is a tempered distribution (the "field configuration")
- (-Δ + m²)⁻¹ is the Green's function/propagator
- The quadratic form is computed in Fourier space as ∫ |f̂(k)|² / (|k|² + m²) dk

### Connection to Osterwalder-Schrader

The **Schwinger functions** (Euclidean Green's functions) are the moments:
  Sₙ(x₁, ..., xₙ) = ∫_{S'} φ(x₁) · · · φ(xₙ) dμ(φ)

For the free field:
  S₂(x, y) = (-Δ + m²)⁻¹(x, y) = ∫ exp(ik·(x-y)) / (|k|² + m²) dk/(2π)ᵈ

These Schwinger functions satisfy the Osterwalder-Schrader axioms (E0'-E4) as
defined in `Reconstruction.lean`, and the OS reconstruction theorem produces the
corresponding Wightman QFT.

### Why Nuclearity is Essential

The measure μ lives on S'(ℝᵈ), which is the **dual** of the nuclear space S(ℝᵈ).
Without nuclearity, Minlos' theorem would not apply and we could not construct μ
from the characteristic functional C. This is why:
- S(ℝᵈ) being nuclear (SchwartzNuclear.lean) is essential
- The Minlos theorem (BochnerMinlos.lean) provides the measure
- The nuclear operator theory (NuclearOperator.lean) and nuclear space definition
  (NuclearSpace.lean) provide the foundational infrastructure

## References

* Glimm-Jaffe, "Quantum Physics" (1987), Ch. 6 (Euclidean field theory)
* Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory" (1974)
* Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" (1973)
* Nelson, "Construction of quantum fields from Markoff fields" (1973)
-/

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped SchwartzMap

variable (d : ℕ) (m : ℝ)

/-! ### The Free Field Quadratic Form -/

/-- The free field quadratic form on Schwartz space:
    Q(f) = ⟨f, (-Δ + m²)⁻¹ f⟩_{L²} = ∫ |f̂(k)|² / (|k|² + m²) dk

    This is computed in Fourier space where the propagator is diagonal.
    The quadratic form is non-negative since (-Δ + m²) is a positive operator
    (for m > 0), hence its inverse is also positive. -/
structure FreeFieldQuadraticForm where
  /-- The mass parameter (must be positive) -/
  mass : ℝ
  mass_pos : 0 < mass
  /-- The spacetime dimension -/
  dim : ℕ
  /-- The quadratic form Q(f) = ⟨f, (-Δ+m²)⁻¹ f⟩ on Schwartz functions.
      Defined via Fourier transform: Q(f) = ∫ |f̂(k)|²/(|k|²+m²) dk -/
  form : 𝓢(EuclideanSpace ℝ (Fin dim), ℝ) → ℝ
  /-- Q is non-negative -/
  form_nonneg : ∀ f, 0 ≤ form f
  /-- Q is a quadratic form: Q(αf) = α² Q(f) -/
  form_smul : ∀ (α : ℝ) (f), form (α • f) = α ^ 2 * form f
  /-- Q satisfies the parallelogram law -/
  form_parallelogram : ∀ f g, form (f + g) + form (f - g) = 2 * form f + 2 * form g
  /-- Q is continuous with respect to the Schwartz topology -/
  form_continuous : Continuous form

/-- The associated bilinear form: B(f,g) = ¼[Q(f+g) - Q(f-g)]. -/
def FreeFieldQuadraticForm.bilinearForm (Q : FreeFieldQuadraticForm) :
    𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →
    𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) → ℝ :=
  fun f g => (Q.form (f + g) - Q.form (f - g)) / 4

/-! ### Free Field Characteristic Functional -/

/-- The free field characteristic functional:
    C(f) = exp(-½ Q(f)) where Q is the free field quadratic form.

    This is a continuous positive-definite functional with C(0) = 1,
    so by Minlos' theorem (applied to the nuclear space S(ℝᵈ)),
    it determines a unique probability measure on S'(ℝᵈ). -/
def FreeFieldCharacteristic (Q : FreeFieldQuadraticForm) :
    𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) → ℂ :=
  fun f => exp (-(1/2 : ℂ) * ↑(Q.form f))

/-- The quadratic form at 0 is 0: Q(0) = Q(0 • f) = 0² Q(f) = 0. -/
theorem FreeFieldQuadraticForm.form_zero (Q : FreeFieldQuadraticForm)
    (f : 𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ)) :
    Q.form 0 = 0 := by
  have h := Q.form_smul 0 f
  simp [zero_smul] at h
  linarith [Q.form_nonneg f]

/-- The free field characteristic functional at 0 equals 1. -/
theorem FreeFieldCharacteristic_zero (Q : FreeFieldQuadraticForm) :
    FreeFieldCharacteristic Q 0 = 1 := by
  simp only [FreeFieldCharacteristic]
  -- Need some f to apply form_zero; use 0 itself via form_smul
  have hform : Q.form 0 = 0 := by
    have h := Q.form_smul 0 0
    simp at h
    linarith [Q.form_nonneg 0]
  rw [hform]
  simp

/-- The free field characteristic functional is continuous. -/
theorem FreeFieldCharacteristic_continuous (Q : FreeFieldQuadraticForm) :
    Continuous (FreeFieldCharacteristic Q) := by
  apply Continuous.cexp
  apply Continuous.mul continuous_const
  exact continuous_ofReal.comp Q.form_continuous

/-- The free field characteristic functional is positive-definite. -/
theorem FreeFieldCharacteristic_posdef (Q : FreeFieldQuadraticForm) :
    IsPositiveDefiniteFn (FreeFieldCharacteristic Q) := by
  sorry

/-- The free field characteristic functional is a `CharacteristicFunctional`. -/
def FreeFieldCharacteristicFunctional (Q : FreeFieldQuadraticForm) :
    CharacteristicFunctional (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ)) where
  toFun := FreeFieldCharacteristic Q
  continuous_toFun := FreeFieldCharacteristic_continuous Q
  positive_definite := FreeFieldCharacteristic_posdef Q
  eval_zero := FreeFieldCharacteristic_zero Q

/-! ### Euclidean Measure via Minlos -/

/-- The **Euclidean field theory measure** for the free scalar field.

    By Minlos' theorem applied to the nuclear space S(ℝᵈ) and the
    free field characteristic functional, there exists a unique probability
    measure μ on the dual space S'(ℝᵈ) (= tempered distributions) such that:

    C(f) = ∫_{S'(ℝᵈ)} exp(i φ(f)) dμ(φ) = exp(-½ ⟨f, (-Δ+m²)⁻¹ f⟩)

    This is a Gaussian measure (the "Euclidean free field measure").

    In constructive QFT, this provides the starting point for:
    1. Defining Schwinger functions as moments of μ
    2. Verifying the OS axioms E0'-E4
    3. Applying the OS reconstruction theorem to get a Wightman QFT -/
theorem euclideanMeasure_exists (Q : FreeFieldQuadraticForm)
    [inst : MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ)] :
    ∃ (μ : Measure (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ)),
      IsProbabilityMeasure μ ∧
      ∀ f, FreeFieldCharacteristic Q f =
        ∫ ω, exp (↑(ω f) * I) ∂μ := by
  haveI : NuclearSpace (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ)) :=
    SchwartzMap.instNuclearSpace Q.dim
  exact minlos_theorem (FreeFieldCharacteristicFunctional Q)

/-! ### Schwinger Functions from the Euclidean Measure -/

/-- The two-point Schwinger function (Euclidean propagator) defined as
    the second moment of the Euclidean measure:
    S₂(x, y) = ∫_{S'} φ(x) φ(y) dμ(φ)

    For the free field, this equals the Green's function:
    S₂(x, y) = (-Δ + m²)⁻¹(x, y) -/
def schwingerTwoPoint (Q : FreeFieldQuadraticForm)
    [MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ)]
    (μ : Measure (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ))
    (δ_x δ_y : 𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ)) : ℂ :=
  ∫ ω : (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ),
    (↑(ω δ_x) : ℂ) * ↑(ω δ_y) ∂μ

/-- The two-point Schwinger function equals the bilinear form of the propagator.
    S₂(f, g) = B(f, g) where B is the bilinear form of Q. -/
theorem schwingerTwoPoint_eq_bilinear (Q : FreeFieldQuadraticForm)
    [MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ)]
    (μ : Measure (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ))
    (_hμ : IsProbabilityMeasure μ)
    (_hchar : ∀ f, FreeFieldCharacteristic Q f =
      ∫ ω : (𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ) →L[ℝ] ℝ), exp (↑(ω f) * I) ∂μ)
    (f g : 𝓢(EuclideanSpace ℝ (Fin Q.dim), ℝ)) :
    schwingerTwoPoint Q μ f g = ↑(Q.bilinearForm f g) := by
  sorry

end

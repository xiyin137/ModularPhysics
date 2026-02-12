/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransform
import ModularPhysics.RigorousQFT.Wightman.NuclearSpaces.BochnerMinlos
import ModularPhysics.RigorousQFT.Wightman.NuclearSpaces.SchwartzNuclear

/-!
# Euclidean Field Theory Measures via Minlos' Theorem

This file connects the nuclear space / Minlos infrastructure to the Osterwalder-Schrader
reconstruction theorem, providing the measure-theoretic foundation for Euclidean QFT.

## Main Definitions

* `freeFieldForm` - The quadratic form Q(f) = ∫ |f̂(k)|² / (|k|² + m²) dk, defined
  concretely using the Fourier transform.
* `freeFieldCharacteristic` - C(f) = exp(-½ Q(f)), the free field characteristic functional.
* `euclideanMeasure_exists` - Existence of the Gaussian probability measure on S'(ℝᵈ).
* `schwingerTwoPoint` - Schwinger functions as moments of the Euclidean measure.

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
open scoped SchwartzMap FourierTransform

variable (d : ℕ) (m : ℝ)

/-! ### The Free Field Quadratic Form -/

/-- The **propagator weight function**: `w(k) = 1 / (‖k‖² + m²)`.

    This is the Fourier-space representation of the Green's function
    `(-Δ + m²)⁻¹` for the Klein-Gordon operator. -/
def propagatorWeight (d : ℕ) (m : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun k => 1 / (‖k‖ ^ 2 + m ^ 2)

/-- The propagator weight is non-negative when m ≥ 0. -/
theorem propagatorWeight_nonneg (_hm : 0 ≤ m) (k : EuclideanSpace ℝ (Fin d)) :
    0 ≤ propagatorWeight d m k := by
  unfold propagatorWeight
  apply div_nonneg one_pos.le
  positivity

/-- The propagator weight is bounded above by 1/m² when m > 0. -/
theorem propagatorWeight_le (hm : 0 < m) (k : EuclideanSpace ℝ (Fin d)) :
    propagatorWeight d m k ≤ 1 / m ^ 2 := by
  unfold propagatorWeight
  apply div_le_div_of_nonneg_left one_pos.le
  · positivity
  · linarith [sq_nonneg ‖k‖]

/-- The free field quadratic form on Schwartz space, defined concretely via
    Fourier transform:

    `Q(f) = ∫ₖ |f̂(k)|² / (‖k‖² + m²) dk`

    where `f̂ = 𝓕 f` is the Fourier transform of f (viewed as a ℂ-valued function).
    This integral is the Fourier-space representation of `⟨f, (-Δ + m²)⁻¹ f⟩_{L²}`. -/
def freeFieldForm (d : ℕ) (m : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℝ :=
  ∫ k : EuclideanSpace ℝ (Fin d),
    ‖𝓕 (fun x => (f x : ℂ)) k‖ ^ 2 * propagatorWeight d m k

/-- The associated bilinear form: B(f,g) = ¼[Q(f+g) - Q(f-g)].

    For the free field, this equals `⟨f, (-Δ+m²)⁻¹ g⟩_{L²}`, i.e.,
    the inner product weighted by the propagator. -/
def freeFieldBilinearForm (d : ℕ) (m : ℝ)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℝ :=
  (freeFieldForm d m (f + g) - freeFieldForm d m (f - g)) / 4

/-! ### Properties of the Free Field Quadratic Form -/

/-- The free field quadratic form is non-negative: Q(f) ≥ 0.
    The integrand |f̂(k)|² / (‖k‖² + m²) is pointwise non-negative. -/
theorem freeFieldForm_nonneg (hm : 0 ≤ m)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    0 ≤ freeFieldForm d m f := by
  unfold freeFieldForm
  apply integral_nonneg
  intro k
  apply mul_nonneg
  · exact sq_nonneg _
  · exact propagatorWeight_nonneg d m hm k

/-- The free field quadratic form at 0 is 0.
    Proof: 0̂ = 0 (Fourier transform of zero), so the integrand vanishes pointwise. -/
theorem freeFieldForm_zero : freeFieldForm d m 0 = 0 := by
  -- Q(0) = ∫ ‖𝓕(0)‖² · w dk = ∫ 0 dk = 0
  -- since 𝓕(0) = 0 (Fourier transform of zero function is zero)
  sorry

/-- The free field quadratic form is homogeneous of degree 2: Q(αf) = α² Q(f).
    This follows from linearity of the Fourier transform: (αf)^ = α f̂. -/
theorem freeFieldForm_smul (α : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    freeFieldForm d m (α • f) = α ^ 2 * freeFieldForm d m f := by
  -- 𝓕(α · f) = α · 𝓕(f) by linearity, so ‖𝓕(αf)(k)‖² = α² · ‖𝓕(f)(k)‖²
  -- Then Q(αf) = ∫ α² · ‖f̂(k)‖² · w(k) dk = α² · Q(f)
  sorry

/-- The free field quadratic form satisfies the parallelogram law. -/
theorem freeFieldForm_parallelogram
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    freeFieldForm d m (f + g) + freeFieldForm d m (f - g) =
    2 * freeFieldForm d m f + 2 * freeFieldForm d m g := by
  sorry

/-- The free field quadratic form is continuous on Schwartz space.
    This follows from:
    1. The Fourier transform is continuous on Schwartz space
    2. The L² norm squared is continuous
    3. The propagator weight 1/(|k|²+m²) is bounded -/
theorem freeFieldForm_continuous (hm : 0 < m) :
    Continuous (freeFieldForm d m) := by
  sorry

/-! ### Free Field Characteristic Functional -/

/-- The free field characteristic functional:
    C(f) = exp(-½ Q(f)) where Q is the free field quadratic form.

    This is a continuous positive-definite functional with C(0) = 1,
    so by Minlos' theorem (applied to the nuclear space S(ℝᵈ)),
    it determines a unique probability measure on S'(ℝᵈ). -/
def freeFieldCharacteristic (d : ℕ) (m : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℂ :=
  exp (-(1/2 : ℂ) * ↑(freeFieldForm d m f))

/-- The free field characteristic functional at 0 equals 1. -/
theorem freeFieldCharacteristic_zero :
    freeFieldCharacteristic d m 0 = 1 := by
  simp only [freeFieldCharacteristic, freeFieldForm_zero]
  simp

/-- The free field characteristic functional is continuous. -/
theorem freeFieldCharacteristic_continuous (hm : 0 < m) :
    Continuous (freeFieldCharacteristic d m) := by
  apply Continuous.cexp
  apply Continuous.mul continuous_const
  exact continuous_ofReal.comp (freeFieldForm_continuous d m hm)

/-- The free field characteristic functional is positive-definite.

    This follows from the fact that exp(-½ Q(f)) where Q is a positive quadratic
    form is positive-definite. The kernel K(f,g) = exp(-½ Q(f-g)) is positive-definite
    because Q is a positive quadratic form, so exp(-½ Q) is a positive-definite function
    (this uses the Schur product theorem and the Taylor expansion of exp). -/
theorem freeFieldCharacteristic_posdef :
    IsPositiveDefiniteFn (freeFieldCharacteristic d m) := by
  sorry

/-- The free field characteristic functional is a `CharacteristicFunctional`. -/
def freeFieldCharacteristicFunctional (hm : 0 < m) :
    CharacteristicFunctional (𝓢(EuclideanSpace ℝ (Fin d), ℝ)) where
  toFun := freeFieldCharacteristic d m
  continuous_toFun := freeFieldCharacteristic_continuous d m hm
  positive_definite := freeFieldCharacteristic_posdef d m
  eval_zero := freeFieldCharacteristic_zero d m

/-! ### Euclidean Measure via Minlos -/

/-- The **Euclidean field theory measure** for the free scalar field.

    By Minlos' theorem applied to the nuclear space S(ℝᵈ) and the
    free field characteristic functional, there exists a unique probability
    measure μ on the dual space S'(ℝᵈ) (= tempered distributions) such that:

    C(f) = ∫_{S'(ℝᵈ)} exp(i φ(f)) dμ(φ) = exp(-½ Q(f))

    This is a Gaussian measure (the "Euclidean free field measure").

    In constructive QFT, this provides the starting point for:
    1. Defining Schwinger functions as moments of μ
    2. Verifying the OS axioms E0'-E4
    3. Applying the OS reconstruction theorem to get a Wightman QFT -/
theorem euclideanMeasure_exists (hm : 0 < m)
    [inst : MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)] :
    ∃ (μ : Measure (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)),
      IsProbabilityMeasure μ ∧
      ∀ (f : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)),
        freeFieldCharacteristic d m f =
        ∫ ω, exp (↑(ω f) * I) ∂μ := by
  haveI : NuclearSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :=
    SchwartzMap.instNuclearSpace d
  exact minlos_theorem (freeFieldCharacteristicFunctional d m hm)

/-! ### Schwinger Functions from the Euclidean Measure -/

/-- The two-point Schwinger function (Euclidean propagator) defined as
    the second moment of the Euclidean measure:
    S₂(x, y) = ∫_{S'} φ(x) φ(y) dμ(φ)

    For the free field, this equals the Green's function:
    S₂(x, y) = (-Δ + m²)⁻¹(x, y) -/
def schwingerTwoPoint
    [MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)]
    (μ : Measure (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ))
    (δ_x δ_y : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) : ℂ :=
  ∫ ω : (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ),
    (↑(ω δ_x) : ℂ) * ↑(ω δ_y) ∂μ

/-- The two-point Schwinger function equals the bilinear form of the propagator.
    S₂(f, g) = B(f, g) where B is the polarized bilinear form of Q. -/
theorem schwingerTwoPoint_eq_bilinear
    [MeasurableSpace (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ)]
    (μ : Measure (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ))
    (_hμ : IsProbabilityMeasure μ)
    (_hchar : ∀ f, freeFieldCharacteristic d m f =
      ∫ ω : (𝓢(EuclideanSpace ℝ (Fin d), ℝ) →L[ℝ] ℝ), exp (↑(ω f) * I) ∂μ)
    (f g : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    schwingerTwoPoint d μ f g = ↑(freeFieldBilinearForm d m f g) := by
  sorry

end

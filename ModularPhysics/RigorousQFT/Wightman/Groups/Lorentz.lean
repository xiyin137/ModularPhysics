/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import ModularPhysics.RigorousQFT.Wightman.Spacetime.Metric

/-!
# The Lorentz Group O(1,d)

This file defines the Lorentz group O(1,d) as the group of linear transformations
preserving the Minkowski metric.

## Main Definitions

* `LorentzGroup d` - The indefinite orthogonal group O(1,d) ⊂ GL(d+1, ℝ)
* `LorentzGroup.IsProper` - Proper Lorentz transformations (det = 1)
* `LorentzGroup.IsOrthochronous` - Orthochronous transformations (Λ₀₀ ≥ 1)
* `LorentzGroup.Restricted` - The restricted Lorentz group SO⁺(1,d)

## Mathematical Background

The Lorentz group O(1,d) consists of all real (d+1)×(d+1) matrices Λ satisfying:
  Λᵀ η Λ = η
where η = diag(-1, +1, ..., +1) is the Minkowski metric.

The group has four connected components, characterized by:
- det(Λ) = ±1 (proper vs improper)
- Λ₀₀ ≥ 1 or Λ₀₀ ≤ -1 (orthochronous vs non-orthochronous)

The restricted Lorentz group SO⁺(1,d) is the identity component (proper orthochronous).

## References

* Weinberg, "The Quantum Theory of Fields", Vol. I, Chapter 2
* Streater-Wightman, "PCT, Spin and Statistics, and All That"
-/

noncomputable section

open Matrix BigOperators

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

/-! ### The Lorentz Group -/

/-- A matrix Λ is a Lorentz transformation if it preserves the Minkowski metric:
    Λᵀ η Λ = η -/
def IsLorentzMatrix (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMatrix d * Λ = minkowskiMatrix d

namespace IsLorentzMatrix

variable {d : ℕ} [NeZero d]

/-- The identity matrix is a Lorentz transformation -/
theorem one : IsLorentzMatrix d (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
  simp only [IsLorentzMatrix, transpose_one, one_mul, mul_one]

/-- The product of two Lorentz transformations is a Lorentz transformation -/
theorem mul {Λ₁ Λ₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h₁ : IsLorentzMatrix d Λ₁) (h₂ : IsLorentzMatrix d Λ₂) :
    IsLorentzMatrix d (Λ₁ * Λ₂) := by
  unfold IsLorentzMatrix at *
  simp only [transpose_mul]
  calc Λ₂ᵀ * Λ₁ᵀ * minkowskiMatrix d * (Λ₁ * Λ₂)
      = Λ₂ᵀ * (Λ₁ᵀ * minkowskiMatrix d * Λ₁) * Λ₂ := by noncomm_ring
    _ = Λ₂ᵀ * minkowskiMatrix d * Λ₂ := by rw [h₁]
    _ = minkowskiMatrix d := h₂

/-- A Lorentz transformation is invertible -/
theorem isUnit (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    IsUnit Λ := by
  rw [Matrix.isUnit_iff_isUnit_det]
  -- From Λᵀ η Λ = η, taking determinants: det(Λ)² det(η) = det(η)
  -- Since det(η) ≠ 0, we get det(Λ)² = 1, so det(Λ) = ±1
  have h_det_sq : Λ.det ^ 2 = 1 := by
    have h_eq := congr_arg Matrix.det h
    simp only [det_mul, det_transpose] at h_eq
    have h_eta_ne : (minkowskiMatrix d).det ≠ 0 := by
      rw [MinkowskiMatrix.det_eq]
      norm_num
    field_simp at h_eq
    linarith [sq_nonneg Λ.det]
  rcases sq_eq_one_iff.mp h_det_sq with hd | hd <;> simp [hd]

/-- The inverse of a Lorentz transformation is also a Lorentz transformation.
    The inverse is given by Λ⁻¹ = η Λᵀ η. -/
theorem inv_eq (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    Λ⁻¹ = minkowskiMatrix d * Λᵀ * minkowskiMatrix d := by
  -- η Λᵀ η is a left inverse, so it equals the matrix inverse
  have hleft : (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ = 1 := by
    unfold IsLorentzMatrix at h
    calc (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ
        = minkowskiMatrix d * Λᵀ * (minkowskiMatrix d * Λ) := by noncomm_ring
      _ = minkowskiMatrix d * (Λᵀ * minkowskiMatrix d * Λ) := by noncomm_ring
      _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
      _ = 1 := MinkowskiMatrix.mul_self d
  exact Matrix.inv_eq_left_inv hleft

/-- The determinant of a Lorentz transformation is ±1 -/
theorem det_eq_pm_one (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    Λ.det = 1 ∨ Λ.det = -1 := by
  -- From Λᵀ η Λ = η, taking determinants:
  -- det(Λᵀ) det(η) det(Λ) = det(η)
  -- det(Λ)² det(η) = det(η)
  -- Since det(η) = -1 ≠ 0, we get det(Λ)² = 1
  have h_det : Λ.det ^ 2 = 1 := by
    have h_eq := congr_arg Matrix.det h
    simp only [det_mul, det_transpose] at h_eq
    have h_eta_ne : (minkowskiMatrix d).det ≠ 0 := by
      rw [MinkowskiMatrix.det_eq]
      norm_num
    field_simp at h_eq
    linarith [sq_nonneg Λ.det]
  rcases sq_eq_one_iff.mp h_det with h1 | h1
  · left; exact h1
  · right; exact h1

/-- The (0,0) component of a Lorentz transformation satisfies |Λ₀₀| ≥ 1 -/
theorem abs_zero_zero_ge_one (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (h : IsLorentzMatrix d Λ) :
    |Λ 0 0| ≥ 1 := by
  -- From (Λᵀ η Λ)₀₀ = η₀₀ = -1, we have:
  -- -Λ₀₀² + Σᵢ>₀ Λᵢ₀² = -1
  -- So Λ₀₀² = 1 + Σᵢ>₀ Λᵢ₀² ≥ 1
  unfold IsLorentzMatrix at h
  -- Extract the (0,0) entry of the equation Λᵀ η Λ = η
  have h00 : (Λᵀ * minkowskiMatrix d * Λ) 0 0 = (minkowskiMatrix d) 0 0 := by
    rw [h]
  simp only [mul_apply, minkowskiMatrix, diagonal_apply, transpose_apply,
    MinkowskiSpace.metricSignature, ite_true] at h00
  -- The inner sum simplifies: only k=j contributes (η is diagonal)
  -- h00 has form: Σⱼ (Σₖ Λₖ₀ · ηₖⱼ) · Λⱼ₀ = -1
  have hinner : ∀ j : Fin (d + 1),
      (∑ k : Fin (d + 1), Λ k 0 * (if k = j then (if k = 0 then (-1:ℝ) else 1) else 0)) =
      (if j = 0 then -1 else 1) * Λ j 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · by_cases hj : j = 0 <;> simp [hj]
    · intro k _ hkj; simp [hkj]
    · simp
  have h00' : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ j 0 * Λ j 0) = -1 := by
    trans (∑ j, (∑ k, Λ k 0 * (if k = j then if k = 0 then (-1:ℝ) else 1 else 0)) * Λ j 0)
    · apply Finset.sum_congr rfl; intro j _; rw [hinner j]
    · exact h00
  -- h00': Σⱼ (if j = 0 then -1 else 1) · Λⱼ₀² = -1
  -- Now h00: Σⱼ (if j = 0 then -1 else 1) · Λⱼ₀ · Λⱼ₀ = -1
  -- i.e., -Λ₀₀² + Σⱼ>₀ Λⱼ₀² = -1, so Λ₀₀² = 1 + Σⱼ>₀ Λⱼ₀²
  have hsplit : (∑ j : Fin (d + 1), (if j = 0 then (-1:ℝ) else 1) * Λ j 0 * Λ j 0) =
      -Λ 0 0 ^ 2 + ∑ j ∈ Finset.univ.filter (· ≠ 0), Λ j 0 ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : Fin (d+1)))]
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton,
      neg_mul, one_mul, sq]
    ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj, sq]
  rw [hsplit] at h00'
  -- h00': -Λ₀₀² + Σⱼ≠₀ Λⱼ₀² = -1
  have hsum_nonneg : (∑ j ∈ Finset.univ.filter (· ≠ 0), Λ j 0 ^ 2) ≥ 0 := by
    apply Finset.sum_nonneg
    intro j _; exact sq_nonneg _
  have hsq : Λ 0 0 ^ 2 ≥ 1 := by linarith
  -- From x² ≥ 1, we get |x| ≥ 1 using x² = |x|² and sqrt monotonicity
  have hsq_abs : |Λ 0 0| ^ 2 ≥ 1 := by rwa [sq_abs]
  nlinarith [sq_nonneg (|Λ 0 0| - 1), sq_nonneg (|Λ 0 0| + 1), abs_nonneg (Λ 0 0)]

end IsLorentzMatrix

/-- The Lorentz group O(1,d) as matrices preserving the Minkowski metric.
    This is the indefinite orthogonal group. -/
def LorentzGroup (d : ℕ) [NeZero d] :=
  { Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ // IsLorentzMatrix d Λ }

namespace LorentzGroup

variable {d : ℕ} [NeZero d]

instance : Coe (LorentzGroup d) (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := ⟨Subtype.val⟩

@[ext]
theorem ext {Λ₁ Λ₂ : LorentzGroup d} (h : Λ₁.val = Λ₂.val) : Λ₁ = Λ₂ :=
  Subtype.ext h

/-- Coercion to matrix -/
theorem toMatrix (Λ : LorentzGroup d) : (Λ : Matrix _ _ ℝ) = Λ.val := rfl

/-- Extensionality for matrix entries -/
theorem ext_entries {Λ₁ Λ₂ : LorentzGroup d} :
    Λ₁ = Λ₂ ↔ ∀ i j, Λ₁.val i j = Λ₂.val i j :=
  ⟨fun h _ _ => by rw [h], fun h => ext (Matrix.ext fun i j => h i j)⟩

/-- Key lemma: (η Λᵀ η) Λ = 1 for Lorentz matrices.
    This follows from Λᵀ η Λ = η by left multiplication by η. -/
theorem lorentz_inv_mul {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : IsLorentzMatrix d Λ) :
    (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ = 1 := by
  unfold IsLorentzMatrix at h
  calc (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) * Λ
      = minkowskiMatrix d * Λᵀ * (minkowskiMatrix d * Λ) := by noncomm_ring
    _ = minkowskiMatrix d * (Λᵀ * minkowskiMatrix d * Λ) := by noncomm_ring
    _ = minkowskiMatrix d * minkowskiMatrix d := by rw [h]
    _ = 1 := MinkowskiMatrix.mul_self d

/-- Key lemma: Λ (η Λᵀ η) = 1 for Lorentz matrices.
    This follows from the left inverse property and invertibility. -/
theorem lorentz_mul_inv {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : IsLorentzMatrix d Λ) :
    Λ * (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) = 1 := by
  have hleft := lorentz_inv_mul h
  -- Use Matrix.mul_eq_one_comm: if M * N = 1 then N * M = 1
  exact mul_eq_one_comm.mp hleft

/-- The inverse formula η Λᵀ η satisfies the Lorentz condition.
    From Λᵀ η Λ = η, we derive (Λ⁻¹)ᵀ η Λ⁻¹ = η. -/
theorem lorentz_inv_isLorentz {Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : IsLorentzMatrix d Λ) :
    IsLorentzMatrix d (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by
  unfold IsLorentzMatrix
  -- Compute the transpose: (η Λᵀ η)ᵀ = η Λ η
  have htrans : (minkowskiMatrix d * Λᵀ * minkowskiMatrix d)ᵀ =
      minkowskiMatrix d * Λ * minkowskiMatrix d := by
    simp only [transpose_mul, MinkowskiMatrix.transpose_eq, transpose_transpose]
    noncomm_ring
  rw [htrans]
  -- We need to show (η Λ η) η (η Λᵀ η) = η
  have hmul := lorentz_mul_inv h
  calc minkowskiMatrix d * Λ * minkowskiMatrix d * minkowskiMatrix d *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d)
      = minkowskiMatrix d * Λ * (minkowskiMatrix d * minkowskiMatrix d) *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by noncomm_ring
    _ = minkowskiMatrix d * Λ * 1 *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by rw [MinkowskiMatrix.mul_self]
    _ = minkowskiMatrix d * Λ *
         (minkowskiMatrix d * Λᵀ * minkowskiMatrix d) := by noncomm_ring
    _ = minkowskiMatrix d * (Λ * (minkowskiMatrix d * Λᵀ * minkowskiMatrix d)) := by noncomm_ring
    _ = minkowskiMatrix d * 1 := by rw [hmul]
    _ = minkowskiMatrix d := by noncomm_ring

/-- The Lorentz group forms a group under matrix multiplication -/
instance : Group (LorentzGroup d) where
  mul Λ₁ Λ₂ := ⟨Λ₁.val * Λ₂.val, IsLorentzMatrix.mul Λ₁.2 Λ₂.2⟩
  one := ⟨1, IsLorentzMatrix.one⟩
  inv Λ := ⟨minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d, lorentz_inv_isLorentz Λ.2⟩
  mul_assoc a b c := ext (Matrix.mul_assoc _ _ _)
  one_mul a := ext (Matrix.one_mul _)
  mul_one a := ext (Matrix.mul_one _)
  inv_mul_cancel a := ext (lorentz_inv_mul a.2)

/-- The determinant of a Lorentz transformation is ±1 -/
theorem det_eq_pm_one (Λ : LorentzGroup d) : Λ.val.det = 1 ∨ Λ.val.det = -1 :=
  IsLorentzMatrix.det_eq_pm_one _ Λ.2

/-! ### Proper and Orthochronous Lorentz Transformations -/

/-- A Lorentz transformation is proper if det(Λ) = 1 -/
def IsProper (Λ : LorentzGroup d) : Prop :=
  Λ.val.det = 1

/-- A Lorentz transformation is orthochronous if Λ₀₀ ≥ 1 -/
def IsOrthochronous (Λ : LorentzGroup d) : Prop :=
  Λ.val 0 0 ≥ 1

/-! ### Properties of Proper Transformations -/

namespace IsProper

/-- The identity is proper: det(I) = 1 -/
theorem one : IsProper (1 : LorentzGroup d) := by
  simp only [IsProper]
  have h : (1 : LorentzGroup d).val = 1 := rfl
  simp [h]

/-- The product of proper transformations is proper: det(ΛΛ') = det(Λ)det(Λ') = 1 -/
theorem mul {Λ₁ Λ₂ : LorentzGroup d} (h₁ : IsProper Λ₁) (h₂ : IsProper Λ₂) :
    IsProper (Λ₁ * Λ₂) := by
  simp only [IsProper] at *
  have h : (Λ₁ * Λ₂).val = Λ₁.val * Λ₂.val := rfl
  simp only [h, det_mul, h₁, h₂, mul_one]

/-- The inverse of a proper transformation is proper: det(Λ⁻¹) = 1/det(Λ) = 1 -/
theorem inv {Λ : LorentzGroup d} (h : IsProper Λ) : IsProper Λ⁻¹ := by
  simp only [IsProper] at *
  -- Λ⁻¹ = η Λᵀ η, so det(Λ⁻¹) = det(η)² det(Λᵀ) = det(Λ) = 1
  have hval : Λ⁻¹.val = minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d := rfl
  simp only [hval, det_mul, det_transpose]
  rw [MinkowskiMatrix.det_eq]
  ring_nf
  exact h

end IsProper

/-! ### Properties of Orthochronous Transformations -/

namespace IsOrthochronous

/-- The identity is orthochronous: I₀₀ = 1 ≥ 1 -/
theorem one : IsOrthochronous (1 : LorentzGroup d) := by
  simp only [IsOrthochronous]
  have h : (1 : LorentzGroup d).val = 1 := rfl
  simp [h]

/-- The product of orthochronous Lorentz transformations is orthochronous.

    This is a fundamental fact about the Lorentz group following from the constraint
    Λᵀ η Λ = η. The (0,0) entry of the product satisfies:
    (Λ₁Λ₂)₀₀ = Σⱼ (Λ₁)₀ⱼ (Λ₂)ⱼ₀

    Using the Lorentz condition and properties of timelike vectors, one shows
    that if (Λ₁)₀₀ ≥ 1 and (Λ₂)₀₀ ≥ 1, then (Λ₁Λ₂)₀₀ ≥ 1.

    The proof uses that the (0,0) entry squared exceeds 1 + sum of spatial entries squared. -/
theorem mul {Λ₁ Λ₂ : LorentzGroup d} (h₁ : IsOrthochronous Λ₁) (h₂ : IsOrthochronous Λ₂) :
    IsOrthochronous (Λ₁ * Λ₂) := by
  simp only [IsOrthochronous] at *
  -- (Λ₁ * Λ₂)₀₀ = Σⱼ (Λ₁)₀ⱼ (Λ₂)ⱼ₀ = (Λ₁)₀₀(Λ₂)₀₀ + Σⱼ>₀ (Λ₁)₀ⱼ(Λ₂)ⱼ₀
  -- Key facts from Lorentz condition:
  -- - First row of Λ₁ is "unit timelike": (Λ₁)₀₀² - Σⱼ>₀(Λ₁)₀ⱼ² = 1
  -- - First column of Λ₂ is "unit timelike": (Λ₂)₀₀² - Σⱼ>₀(Λ₂)ⱼ₀² = 1
  -- By Cauchy-Schwarz: |Σⱼ>₀ (Λ₁)₀ⱼ(Λ₂)ⱼ₀| ≤ √((Λ₁)₀₀²-1) · √((Λ₂)₀₀²-1)
  -- For a,b ≥ 1: ab - √(a²-1)√(b²-1) ≥ 1 (hyperbolic identity: cosh(α-β) ≥ 1)
  -- The full proof requires establishing these facts from the Lorentz condition.
  sorry

/-- The inverse of an orthochronous transformation is orthochronous.

    Since Λ⁻¹ = η Λᵀ η for Lorentz transformations, and the (0,0) entry of
    a transpose equals the original (0,0) entry, we have (Λ⁻¹)₀₀ = (Λ)₀₀ ≥ 1.

    Proof sketch: For diagonal η with η₀₀ = -1 and ηᵢᵢ = 1 for i > 0,
    (η Λᵀ η)₀₀ = Σⱼ η₀ⱼ (Σₖ Λₖⱼ ηₖ₀) = η₀₀ · Λ₀₀ · η₀₀ = (-1)·Λ₀₀·(-1) = Λ₀₀ ≥ 1. -/
theorem inv {Λ : LorentzGroup d} (h : IsOrthochronous Λ) : IsOrthochronous Λ⁻¹ := by
  simp only [IsOrthochronous] at *
  have hval : Λ⁻¹.val = minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d := rfl
  -- The (0,0) entry of η Λᵀ η equals Λ₀₀ due to diagonal structure of η
  have hentry : (minkowskiMatrix d * Λ.valᵀ * minkowskiMatrix d) 0 0 = Λ.val 0 0 := by
    -- For diagonal η, (η Aᵀ η)₀₀ = η₀₀ · A₀₀ · η₀₀ = (-1)·A₀₀·(-1) = A₀₀
    simp only [mul_apply, minkowskiMatrix, diagonal_apply, transpose_apply,
      MinkowskiSpace.metricSignature]
    simp only [ite_true]
    -- The inner sum: only k=0 contributes (diagonal η)
    have hinner : ∀ x : Fin (d + 1),
        (∑ k : Fin (d + 1), (if (0 : Fin (d+1)) = k then (-1 : ℝ) else 0) * Λ.val x k) =
        -Λ.val x 0 := by
      intro x
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [hk.symm]
      · simp
    -- Rewrite using hinner
    have hsum : ∀ x : Fin (d + 1),
        (∑ k, (if (0 : Fin (d+1)) = k then (-1 : ℝ) else 0) * Λ.val x k) *
        (if x = 0 then if x = 0 then (-1 : ℝ) else 1 else 0) =
        (if x = 0 then Λ.val 0 0 else 0) := by
      intro x
      rw [hinner x]
      by_cases hx : x = 0
      · simp [hx]
      · simp [hx]
    trans (∑ x : Fin (d + 1), if x = 0 then Λ.val 0 0 else 0)
    · exact Finset.sum_congr rfl (fun x _ => hsum x)
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hval, hentry]
  exact h

end IsOrthochronous

/-- The restricted Lorentz group SO⁺(1,d) consists of proper orthochronous transformations -/
def Restricted : Subgroup (LorentzGroup d) where
  carrier := { Λ | IsProper Λ ∧ IsOrthochronous Λ }
  mul_mem' ha hb := ⟨IsProper.mul ha.1 hb.1, IsOrthochronous.mul ha.2 hb.2⟩
  one_mem' := ⟨IsProper.one, IsOrthochronous.one⟩
  inv_mem' ha := ⟨IsProper.inv ha.1, IsOrthochronous.inv ha.2⟩

/-! ### Special Elements -/

/-- Space inversion (parity): P = diag(+1, -1, -1, ..., -1)
    Action: (t, x) ↦ (t, -x). Keeps time, flips spatial coordinates.
    Note: P = -η in the mostly positive convention. -/
def parity : LorentzGroup d := ⟨
  diagonal (fun i => if i = 0 then 1 else -1),
  by
    -- Pᵀ η P = P η P (since P diagonal) = η because Pᵢᵢ² ηᵢᵢ = ηᵢᵢ
    -- Key: P = -η, so Pᵀ η P = (-η) η (-η) = η η η = η
    unfold IsLorentzMatrix minkowskiMatrix MinkowskiSpace.metricSignature
    -- P = -η in the mostly positive convention
    have hP : diagonal (fun i => if i = 0 then (1 : ℝ) else -1) =
        -diagonal (MinkowskiSpace.metricSignature d) := by
      ext i j
      simp only [diagonal_apply, MinkowskiSpace.metricSignature, neg_apply]
      by_cases hi : i = j
      · subst hi; by_cases h0 : i = 0 <;> simp [h0]
      · simp [hi]
    rw [hP]
    simp only [transpose_neg, diagonal_transpose, neg_mul, mul_neg, neg_neg]
    -- Now: η η η = η
    calc diagonal (MinkowskiSpace.metricSignature d) *
           diagonal (MinkowskiSpace.metricSignature d) *
           diagonal (MinkowskiSpace.metricSignature d)
        = (diagonal (MinkowskiSpace.metricSignature d) *
           diagonal (MinkowskiSpace.metricSignature d)) *
           diagonal (MinkowskiSpace.metricSignature d) := by noncomm_ring
      _ = 1 * diagonal (MinkowskiSpace.metricSignature d) := by
          rw [← MinkowskiMatrix.mul_self d]; rfl
      _ = diagonal (MinkowskiSpace.metricSignature d) := one_mul _⟩

/-- Time reversal: T = diag(-1, +1, +1, ..., +1)
    Action: (t, x) ↦ (-t, x). Flips time, keeps spatial coordinates.
    Note: T = η in the mostly positive convention. -/
def timeReversal : LorentzGroup d := ⟨
  diagonal (fun i => if i = 0 then -1 else 1),
  by
    -- T = η, so Tᵀ η T = η η η = η (since η² = 1)
    unfold IsLorentzMatrix minkowskiMatrix MinkowskiSpace.metricSignature
    have heq : diagonal (fun i => if i = 0 then -1 else (1 : ℝ)) =
        diagonal (MinkowskiSpace.metricSignature d) := by
      ext i j
      simp only [diagonal_apply, MinkowskiSpace.metricSignature]
    rw [heq]
    -- Now need ηᵀ η η = η, i.e., η η η = η (since ηᵀ = η)
    simp only [diagonal_transpose]
    calc diagonal (MinkowskiSpace.metricSignature d) *
           diagonal (MinkowskiSpace.metricSignature d) *
           diagonal (MinkowskiSpace.metricSignature d)
        = (diagonal (MinkowskiSpace.metricSignature d) *
           diagonal (MinkowskiSpace.metricSignature d)) *
           diagonal (MinkowskiSpace.metricSignature d) := by noncomm_ring
      _ = 1 * diagonal (MinkowskiSpace.metricSignature d) := by
          rw [← MinkowskiMatrix.mul_self d]; rfl
      _ = diagonal (MinkowskiSpace.metricSignature d) := one_mul _⟩

/-- PT = diag(-1, -1, ..., -1) = -I, the total inversion.
    Action: (t, x) ↦ (-t, -x). -/
theorem parity_mul_timeReversal : parity (d := d) * timeReversal = ⟨-1, by
    -- (-I)ᵀ η (-I) = I η I = η
    unfold IsLorentzMatrix
    simp only [transpose_neg, transpose_one, neg_mul, one_mul, mul_neg, mul_one, neg_neg]⟩ := by
  ext i j
  -- Unfold and compute the matrix product
  unfold parity timeReversal
  change ((diagonal (fun i : Fin (d+1) => if i = 0 then (1:ℝ) else -1)) *
          (diagonal (fun i : Fin (d+1) => if i = 0 then (-1:ℝ) else 1))) i j =
         ((-1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)) i j
  rw [diagonal_mul_diagonal]
  simp only [diagonal_apply, neg_apply, one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    by_cases h0 : i = 0 <;> simp [h0]
  · simp [hij]

end LorentzGroup

/-! ### Notation -/

/-- Standard notation for the 3+1 dimensional Lorentz group -/
abbrev Lorentz4 := LorentzGroup 3

end


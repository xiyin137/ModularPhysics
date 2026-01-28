/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# Spectral Measures via Stieltjes Functions

This file connects spectral measures to Mathlib's `StieltjesFunction` infrastructure.

For a self-adjoint operator T with spectral measure P:
- The function F_x(λ) = ⟨x, P((-∞, λ]) x⟩ is monotone non-decreasing and right-continuous
- This is exactly what `StieltjesFunction` captures
- The associated measure is the spectral measure μ_{x,x}

For the complex spectral measure μ_{x,y}(E) = ⟨x, P(E) y⟩, we use polarization:
  μ_{x,y} = (1/4)[μ_{x+y,x+y} - μ_{x-y,x-y} + i·μ_{x+iy,x+iy} - i·μ_{x-iy,x-iy}]

## Main Definitions

* `SpectralDistribution` - The distribution function F_x(λ) = ⟨x, P((-∞, λ]) x⟩
* `SpectralDistribution.toStieltjes` - Conversion to `StieltjesFunction`
* `SpectralDistribution.toMeasure` - The spectral measure μ_{x,x}

## Main Results

* `SpectralDistribution.measure_Ioc` - μ_{x,x}((a, b]) = F_x(b) - F_x(a)
* `SpectralDistribution.measure_Icc` - μ_{x,x}([a, b]) for closed intervals
* Polarization identity for complex spectral measures

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VII
* Mathlib's `MeasureTheory.Measure.Stieltjes`
-/

noncomputable section

open scoped ENNReal NNReal
open Set Filter Topology MeasureTheory

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Spectral Distribution Functions -/

/-- A spectral distribution function is a right-continuous, monotone non-decreasing function
    F : ℝ → ℝ with F(-∞) = 0 and F(+∞) = some bound.

    This arises from F(λ) = ⟨x, P((-∞, λ]) x⟩ for a spectral measure P and vector x. -/
structure SpectralDistribution where
  /-- The distribution function -/
  toFun : ℝ → ℝ
  /-- Monotone non-decreasing -/
  mono : Monotone toFun
  /-- Right-continuous -/
  right_continuous : ∀ x, ContinuousWithinAt toFun (Set.Ici x) x
  /-- Non-negative values -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- Bounded above -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  /-- F(x) ≤ bound for all x -/
  le_bound : ∀ x, toFun x ≤ bound
  /-- F(x) → 0 as x → -∞ -/
  tendsto_neg_infty : Tendsto toFun atBot (nhds 0)
  /-- F(x) → bound as x → +∞ -/
  tendsto_pos_infty : Tendsto toFun atTop (nhds bound)

namespace SpectralDistribution

variable (F : SpectralDistribution)

/-- Convert a spectral distribution to a Stieltjes function. -/
def toStieltjes : StieltjesFunction ℝ where
  toFun := F.toFun
  mono' := F.mono
  right_continuous' := F.right_continuous

/-- The measure associated to a spectral distribution function.
    This is the unique measure with μ((a, b]) = F(b) - F(a). -/
def toMeasure : Measure ℝ :=
  F.toStieltjes.measure

/-- The measure of a half-open interval (a, b]. -/
theorem measure_Ioc (a b : ℝ) :
    F.toMeasure (Set.Ioc a b) = ENNReal.ofReal (F.toFun b - F.toFun a) := by
  unfold toMeasure toStieltjes
  exact StieltjesFunction.measure_Ioc _ a b

/-- The measure of (a, b] is non-negative because F is monotone. -/
theorem measure_Ioc_nonneg (a b : ℝ) (hab : a ≤ b) :
    0 ≤ F.toFun b - F.toFun a :=
  sub_nonneg.mpr (F.mono hab)

/-- The measure of a closed interval [a, b]. -/
theorem measure_Icc (a b : ℝ) :
    F.toMeasure (Set.Icc a b) =
      ENNReal.ofReal (F.toFun b - Function.leftLim F.toFun a) := by
  unfold toMeasure toStieltjes
  exact StieltjesFunction.measure_Icc _ a b

/-- The measure of {a} (point mass). -/
theorem measure_singleton (a : ℝ) :
    F.toMeasure {a} = ENNReal.ofReal (F.toFun a - Function.leftLim F.toFun a) := by
  unfold toMeasure toStieltjes
  exact StieltjesFunction.measure_singleton _ a

/-- The measure is finite. -/
theorem measure_finite : F.toMeasure Set.univ < ⊤ := by
  have h := StieltjesFunction.measure_univ F.toStieltjes F.tendsto_neg_infty F.tendsto_pos_infty
  rw [toMeasure, h]
  exact ENNReal.ofReal_lt_top

/-- The measure is σ-finite (in fact finite). -/
instance : IsFiniteMeasure F.toMeasure where
  measure_univ_lt_top := F.measure_finite

end SpectralDistribution

/-! ### Construction from Projection-Valued Measures -/

/-- A projection-valued measure (PVM) on ℝ into B(H).

    For a self-adjoint operator T, the spectral theorem gives a unique PVM P with
    T = ∫ λ dP(λ). -/
structure ProjectionValuedMeasure (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection for each Borel set -/
  proj : Set ℝ → (H →L[ℂ] H)
  /-- P(∅) = 0 -/
  empty : proj ∅ = 0
  /-- P(ℝ) = I -/
  univ : proj Set.univ = ContinuousLinearMap.id ℂ H
  /-- P(E)² = P(E) (idempotent) -/
  idempotent : ∀ E, proj E ∘L proj E = proj E
  /-- P(E)* = P(E) (self-adjoint) -/
  selfAdjoint : ∀ E, (proj E).adjoint = proj E
  /-- P(E ∩ F) = P(E) ∘ P(F) (multiplicative) -/
  inter : ∀ E F, proj (E ∩ F) = proj E ∘L proj F
  /-- σ-additivity in the strong operator topology -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, proj (E i) x)
      atTop (nhds (proj (⋃ i, E i) x))

namespace ProjectionValuedMeasure

variable [CompleteSpace H] (P : ProjectionValuedMeasure H)

/-- P applied to disjoint sets gives orthogonal ranges: for disjoint E, F,
    ⟨P(E)x, P(F)x⟩ = 0. This follows from P(E ∩ F) = P(E) P(F) and E ∩ F = ∅. -/
theorem proj_orthogonal (x : H) (E F : Set ℝ) (hEF : Disjoint E F) :
    @inner ℂ H _ (P.proj E x) (P.proj F x) = 0 := by
  have h1 : P.proj (E ∩ F) = P.proj E ∘L P.proj F := P.inter E F
  have h2 : E ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.mp hEF
  rw [h2, P.empty] at h1
  -- P(E) P(F) = 0, so ⟨P(E)x, P(F)x⟩ = ⟨x, P(E)* P(F) x⟩ = ⟨x, P(E) P(F) x⟩ = 0
  -- Use adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
  -- So ⟨P(E)x, P(F)x⟩ = ⟨x, P(E)* P(F)x⟩ (by adjoint_inner_right with A = P(E), y = P(F)x)
  have h3 : @inner ℂ H _ (P.proj E x) (P.proj F x) =
      @inner ℂ H _ x ((P.proj E).adjoint (P.proj F x)) :=
    (ContinuousLinearMap.adjoint_inner_right (P.proj E) x (P.proj F x)).symm
  rw [h3, P.selfAdjoint E]
  -- Now: ⟨x, P(E)(P(F)x)⟩ = ⟨x, (P(E) ∘ P(F)) x⟩ = ⟨x, 0⟩ = 0
  simp only [← ContinuousLinearMap.comp_apply, ← h1, ContinuousLinearMap.zero_apply,
    inner_zero_right]

/-- For a sequence of disjoint sets E_n, the partial sums ∑_{k<n} P(E_k) x form a Cauchy sequence. -/
theorem proj_disjoint_cauchy (x : H) (E : ℕ → Set ℝ) (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j)) :
    CauchySeq (fun n => ∑ i ∈ Finset.range n, P.proj (E i) x) := by
  -- The sequence converges by σ-additivity, hence is Cauchy
  exact (P.sigma_additive E hE x).cauchySeq

/-- For decreasing sets E_n with ⋂ E_n = E, P(E_n) x → P(E) x in the norm topology.

    This is the monotone convergence theorem for projection-valued measures.
    The proof uses σ-additivity on the "difference" sets F_k = E_k \ E_{k+1}. -/
theorem proj_decreasing_tendsto (x : H) (E : ℕ → Set ℝ) (S : Set ℝ)
    (hE_dec : ∀ n, E (n + 1) ⊆ E n)
    (hE_inter : ⋂ n, E n = S) :
    Tendsto (fun n => P.proj (E n) x) atTop (nhds (P.proj S x)) := by
  -- The proof uses σ-additivity on the "difference" sets F_k = E_k \ E_{k+1}.
  -- These are disjoint and E_0 \ S = ⋃_k F_k.
  -- By σ-additivity, ∑_k P(F_k) x → P(E_0 \ S) x.
  -- P(E_n) x = P(S) x + P(E_n \ S) x (by finite additivity)
  -- E_n \ S = ⋃_{k≥n} F_k, so P(E_n \ S) x is a tail of the convergent series.
  -- Hence P(E_n \ S) x → 0, so P(E_n) x → P(S) x.
  -- Full formalization requires infrastructure for finite additivity and tail decay.
  sorry

/-- ⟨x, P(E)x⟩ is real and non-negative for any projection P(E). -/
theorem inner_proj_nonneg (x : H) (E : Set ℝ) :
    0 ≤ (@inner ℂ H _ x (P.proj E x)).re := by
  -- P(E) is a self-adjoint idempotent, hence ⟨x, P(E)x⟩ = ‖P(E)x‖² ≥ 0
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  -- ⟨x, P(E)x⟩ = ⟨P(E)*x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

/-- ⟨x, P(E)x⟩ is actually real (imaginary part is 0). -/
theorem inner_proj_real (x : H) (E : Set ℝ) :
    (@inner ℂ H _ x (P.proj E x)).im = 0 := by
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- ⟨x, P(E)x⟩.re = ‖P(E)x‖² for projections. -/
theorem inner_proj_eq_norm_sq (x : H) (E : Set ℝ) :
    (@inner ℂ H _ x (P.proj E x)).re = ‖P.proj E x‖^2 := by
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, sq]
  exact inner_self_eq_norm_mul_norm (𝕜 := ℂ) (P.proj E x)

/-- ⟨x, P(E)x⟩ ≤ ‖x‖² because P(E) ≤ I. -/
theorem inner_proj_le_norm_sq (x : H) (E : Set ℝ) :
    (@inner ℂ H _ x (P.proj E x)).re ≤ ‖x‖^2 := by
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, inner_self_eq_norm_sq_to_K]
  norm_cast
  -- ‖P(E)x‖² ≤ ‖x‖² because P(E) is a contraction (as a projection)
  have hP_contraction : ‖P.proj E x‖ ≤ ‖x‖ := by
    -- P(E) = P(E)² implies ‖P(E)x‖ ≤ ‖x‖
    by_cases hPx : P.proj E x = 0
    · rw [hPx, norm_zero]
      exact norm_nonneg x
    · have hPx_pos : 0 < ‖P.proj E x‖ := norm_pos_iff.mpr hPx
      have hcs : (@inner ℂ H _ x (P.proj E x)).re ≤ ‖x‖ * ‖P.proj E x‖ := by
        calc (@inner ℂ H _ x (P.proj E x)).re
            ≤ |(@inner ℂ H _ x (P.proj E x)).re| := le_abs_self _
          _ ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := Complex.abs_re_le_norm _
          _ ≤ ‖x‖ * ‖P.proj E x‖ := norm_inner_le_norm x (P.proj E x)
      rw [h3] at hcs
      -- Now hcs : (@inner ℂ H _ (P.proj E x) (P.proj E x)).re ≤ ‖x‖ * ‖P.proj E x‖
      -- Use inner_self_eq_norm_mul_norm: re ⟪y, y⟫ = ‖y‖ * ‖y‖
      have h5 : (@inner ℂ H _ (P.proj E x) (P.proj E x)).re = ‖P.proj E x‖ * ‖P.proj E x‖ := by
        simp only [← RCLike.re_to_complex]
        exact inner_self_eq_norm_mul_norm (P.proj E x)
      rw [h5] at hcs
      -- hcs : ‖P.proj E x‖ * ‖P.proj E x‖ ≤ ‖x‖ * ‖P.proj E x‖
      calc ‖P.proj E x‖ = (‖P.proj E x‖ * ‖P.proj E x‖) / ‖P.proj E x‖ := by
            field_simp [hPx_pos.ne']
        _ ≤ (‖x‖ * ‖P.proj E x‖) / ‖P.proj E x‖ := by
            apply div_le_div_of_nonneg_right hcs hPx_pos.le
        _ = ‖x‖ := by field_simp [hPx_pos.ne']
  calc ‖P.proj E x‖^2 ≤ ‖x‖^2 := sq_le_sq' (by linarith [norm_nonneg (P.proj E x)])
                                            hP_contraction

/-- The spectral distribution function for a vector x:
    F_x(t) = ⟨x, P((-∞, t]) x⟩ -/
def distributionFunction (x : H) : SpectralDistribution where
  toFun := fun t => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
  mono := by
    intro a b hab
    -- Simplify the function application
    simp only
    -- Use inner_proj_eq_norm_sq: ⟨x, P(E) x⟩.re = ‖P(E) x‖²
    rw [P.inner_proj_eq_norm_sq, P.inner_proj_eq_norm_sq]
    -- Goal: ‖P(Iic a) x‖² ≤ ‖P(Iic b) x‖²
    have hsub : Set.Iic a ⊆ Set.Iic b := Set.Iic_subset_Iic.mpr hab
    -- P(Iic a) = P(Iic a ∩ Iic b) = P(Iic a) ∘ P(Iic b)
    have h1 : Set.Iic a ∩ Set.Iic b = Set.Iic a := Set.inter_eq_left.mpr hsub
    have h2 : P.proj (Set.Iic a) = P.proj (Set.Iic a) ∘L P.proj (Set.Iic b) := by
      rw [← P.inter, h1]
    -- P(Iic a) x = P(Iic a) (P(Iic b) x)
    have h3 : P.proj (Set.Iic a) x = P.proj (Set.Iic a) (P.proj (Set.Iic b) x) := by
      conv_lhs => rw [h2]
      simp only [ContinuousLinearMap.comp_apply]
    -- Projections are contractions: ‖P(E) y‖ ≤ ‖y‖
    have hcontract : ‖P.proj (Set.Iic a) (P.proj (Set.Iic b) x)‖ ≤ ‖P.proj (Set.Iic b) x‖ := by
      have hP := P.idempotent (Set.Iic a)
      have hPsa := P.selfAdjoint (Set.Iic a)
      set y := P.proj (Set.Iic b) x with hy_def
      by_cases hy : P.proj (Set.Iic a) y = 0
      · rw [hy_def, hy, norm_zero]
        exact norm_nonneg _
      · have hpos : 0 < ‖P.proj (Set.Iic a) y‖ := norm_pos_iff.mpr hy
        have hinner : (@inner ℂ H _ y (P.proj (Set.Iic a) y)).re = ‖P.proj (Set.Iic a) y‖^2 :=
          P.inner_proj_eq_norm_sq y (Set.Iic a)
        have hcs : (@inner ℂ H _ y (P.proj (Set.Iic a) y)).re ≤ ‖y‖ * ‖P.proj (Set.Iic a) y‖ := by
          calc (@inner ℂ H _ y (P.proj (Set.Iic a) y)).re
              ≤ |(@inner ℂ H _ y (P.proj (Set.Iic a) y)).re| := le_abs_self _
            _ ≤ ‖@inner ℂ H _ y (P.proj (Set.Iic a) y)‖ := Complex.abs_re_le_norm _
            _ ≤ ‖y‖ * ‖P.proj (Set.Iic a) y‖ := norm_inner_le_norm y (P.proj (Set.Iic a) y)
        rw [hinner] at hcs
        calc ‖P.proj (Set.Iic a) y‖
            = ‖P.proj (Set.Iic a) y‖^2 / ‖P.proj (Set.Iic a) y‖ := by field_simp [hpos.ne']
          _ ≤ (‖y‖ * ‖P.proj (Set.Iic a) y‖) / ‖P.proj (Set.Iic a) y‖ := by
              apply div_le_div_of_nonneg_right hcs hpos.le
          _ = ‖y‖ := by field_simp [hpos.ne']
    -- ‖P(Iic a) x‖² ≤ ‖P(Iic b) x‖²
    rw [h3]
    apply sq_le_sq' (by linarith [norm_nonneg (P.proj (Set.Iic a) (P.proj (Set.Iic b) x))])
    exact hcontract
  right_continuous := by
    intro t
    -- Right-continuity follows from σ-additivity via proj_decreasing_tendsto.
    -- The sets E_n := Iic (t + 1/(n+1)) form a decreasing sequence with ⋂_n E_n = Iic t.
    -- By proj_decreasing_tendsto, P(E_n) x → P(Iic t) x in norm.
    -- Hence ⟨x, P(E_n) x⟩.re → ⟨x, P(Iic t) x⟩.re.
    -- Since F is monotone, the sequential limit implies ContinuousWithinAt.
    sorry
  nonneg := fun t => P.inner_proj_nonneg x (Set.Iic t)
  bound := ‖x‖^2
  bound_nonneg := sq_nonneg _
  le_bound := fun t => P.inner_proj_le_norm_sq x (Set.Iic t)
  tendsto_neg_infty := by
    -- P((-∞, -n]) → 0 as n → ∞
    sorry
  tendsto_pos_infty := by
    -- P((-∞, n]) → I as n → ∞, so ⟨x, Px⟩ → ⟨x, x⟩ = ‖x‖²
    -- Use inner_proj_eq_norm_sq: ⟨x, P(E) x⟩.re = ‖P(E) x‖²
    have heq : ∀ t, (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re = ‖P.proj (Set.Iic t) x‖^2 :=
      fun t => P.inner_proj_eq_norm_sq x (Set.Iic t)
    simp_rw [heq]
    -- Goal: Tendsto (fun t => ‖P.proj (Iic t) x‖^2) atTop (nhds (‖x‖^2))
    -- This follows from: P(Iic n) x → x in norm, and ‖·‖² is continuous
    -- P(Iic n) x → P(ℝ) x = x because ⋃ₙ Iic n = ℝ and projections converge monotonically
    -- Formal proof requires monotone convergence for projection-valued measures
    sorry

/-- The spectral measure μ_{x,x} for a vector x. -/
def diagonalMeasure (x : H) : Measure ℝ :=
  (P.distributionFunction x).toMeasure

/-- The complex spectral measure μ_{x,y} defined via polarization. -/
def complexMeasure (x y : H) (E : Set ℝ) : ℂ :=
  -- Polarization identity:
  -- 4⟨x, Py⟩ = ⟨x+y, P(x+y)⟩ - ⟨x-y, P(x-y)⟩ + i⟨x+iy, P(x+iy)⟩ - i⟨x-iy, P(x-iy)⟩
  let μpp := (P.diagonalMeasure (x + y) E).toReal
  let μmm := (P.diagonalMeasure (x - y) E).toReal
  let μpi := (P.diagonalMeasure (x + Complex.I • y) E).toReal
  let μmi := (P.diagonalMeasure (x - Complex.I • y) E).toReal
  (1/4 : ℂ) * (μpp - μmm + Complex.I * μpi - Complex.I * μmi)

/-- The complex measure agrees with the inner product on projections. -/
theorem complexMeasure_eq_inner (x y : H) (E : Set ℝ) :
    P.complexMeasure x y E = @inner ℂ H _ x (P.proj E y) := by
  -- Follows from polarization identity for inner products
  sorry

end ProjectionValuedMeasure

end

/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Unbounded.Spectral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Convergence Theorems for Spectral Integrals

This file provides convergence theorems for the spectral functional calculus
`functionalCalculus P f` defined in `Unbounded/Spectral.lean`.

## Main Results

* `functionalCalculus_norm_sq`: The **norm-squared identity**:
    `‖f(T)x‖² = ∫ |f|² dμ_x` where `μ_x` is the diagonal spectral measure.
  This is the key bridge between operator norms and scalar integrals.

* `functionalCalculus_tendsto_SOT`: **Dominated convergence in SOT**:
    If `fₙ → f` pointwise and `|fₙ| ≤ g` with `g²` integrable,
    then `fₙ(T)x → f(T)x` for all x.

## Mathematical Background

The norm-squared identity is fundamental:
  `‖f(T)x‖² = ⟨f(T)x, f(T)x⟩ = ⟨x, f̄(T)f(T)x⟩ = ⟨x, |f|²(T)x⟩ = ∫ |f|² dμ_x`

This uses:
- `functionalCalculus_star`: `f(T)* = f̄(T)`
- `functionalCalculus_mul`: `f(T)g(T) = (fg)(T)`
- `functionalCalculus_inner_self`: `⟨x, f(T)x⟩ = ∫ f dμ_x`

The dominated convergence theorem then follows:
  `‖fₙ(T)x - f(T)x‖² = ‖(fₙ-f)(T)x‖² = ∫ |fₙ-f|² dμ_x → 0`
by the scalar dominated convergence theorem (Mathlib's
`tendsto_integral_of_dominated_convergence`).

## Coordination with existing infrastructure

- `vNA/Unbounded/Spectral.lean`: `SpectralMeasure`, `functionalCalculus`,
  `functionalCalculus_mul`, `functionalCalculus_star`, `diagonalMeasure`,
  `functionalCalculus_inner_self`
- `vNA/MeasureTheory/SpectralIntegral.lean`: `sesquilinearToOperator`
- `vNA/MeasureTheory/SpectralStieltjes.lean`: `ProjectionValuedMeasure`, `diagonalMeasure`

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
-/

noncomputable section

open MeasureTheory Complex Filter Topology SpectralMeasure
open scoped InnerProduct ComplexConjugate

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Norm-squared identity -/

/-- The norm-squared identity for the spectral functional calculus:
    `‖f(T)x‖² = ∫ |f(t)|² dμ_x(t)`

    where `μ_x` is the diagonal spectral measure `μ_x(E) = ⟨x, P(E)x⟩`.

    **Proof:**
    ```
    ⟪f(T)x, f(T)x⟫ = (↑‖f(T)x‖)²       (inner_self_eq_norm_sq_to_K)
    ⟪f(T)x, f(T)x⟫ = ⟪x, f(T)*f(T)x⟫   (adjoint)
                     = ⟪x, (f̄·f)(T)x⟫    (star + mul)
                     = ∫ f̄·f dμ_x         (functionalCalculus_inner_self)
                     = ∫ ↑‖f‖² dμ_x       (f̄·f = ‖f‖²)
                     = ↑(∫ ‖f‖² dμ_x)     (integral_ofReal)
    ``` -/
theorem functionalCalculus_norm_sq (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_int : ∀ z : H, Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    -- Integrability and boundedness of star f
    (hsf_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z))
    (hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f) t‖ ≤ M)
    -- Integrability and boundedness of |f|² = (star f) * f
    (hff_int : ∀ z : H, Integrable ((star ∘ f) * f) (P.diagonalMeasure z))
    (hff_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖((star ∘ f) * f) t‖ ≤ M)
    -- Measurability of f (for multiplicativity)
    (hf_meas : Measurable f)
    (x : H) :
    (‖functionalCalculus P f hf_int hf_bdd x‖ : ℝ)^2 =
    ∫ t, ‖f t‖^2 ∂(P.diagonalMeasure x) := by
  -- Step 1: ‖v‖² = re⟨v,v⟩
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  -- Step 2: ⟨f(T)x, f(T)x⟩ = ⟨x, f(T)*f(T)x⟩
  have h2 : @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd x)
      (functionalCalculus P f hf_int hf_bdd x) =
      @inner ℂ H _ x ((functionalCalculus P f hf_int hf_bdd).adjoint
        (functionalCalculus P f hf_int hf_bdd x)) := by
    rw [ContinuousLinearMap.adjoint_inner_right]
  -- Step 3: f(T)* = f̄(T)
  have h3 : (functionalCalculus P f hf_int hf_bdd).adjoint =
      functionalCalculus P (star ∘ f) hsf_int hsf_bdd :=
    functionalCalculus_star P f hf_int hf_bdd hsf_int hsf_bdd
  -- Step 4: f̄(T)·f(T) = (f̄·f)(T)
  have h4 : functionalCalculus P (star ∘ f) hsf_int hsf_bdd ∘L
      functionalCalculus P f hf_int hf_bdd =
      functionalCalculus P ((star ∘ f) * f) hff_int hff_bdd := by
    rw [← functionalCalculus_mul P (star ∘ f) f hsf_int hsf_bdd hf_int hf_bdd
      hff_int hff_bdd hf_meas]
  -- Combine steps 2-4: ⟨f(T)x, f(T)x⟩ = ⟨x, (f̄f)(T)x⟩
  have h234 : @inner ℂ H _ (functionalCalculus P f hf_int hf_bdd x)
      (functionalCalculus P f hf_int hf_bdd x) =
      @inner ℂ H _ x (functionalCalculus P ((star ∘ f) * f) hff_int hff_bdd x) := by
    rw [h2, h3]
    congr 1
    have := congrFun (congrArg DFunLike.coe h4) x
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this
  -- Step 5: ⟨x, (f̄f)(T)x⟩ = ∫ (f̄f) dμ_x  (via functionalCalculus_inner_self)
  have h5 : @inner ℂ H _ x (functionalCalculus P ((star ∘ f) * f) hff_int hff_bdd x) =
      ∫ t, ((star ∘ f) * f) t ∂(P.diagonalMeasure x) :=
    functionalCalculus_inner_self P ((star ∘ f) * f) hff_int hff_bdd x
  -- Step 6: (f̄·f)(t) = ↑‖f(t)‖² (as ℂ)
  -- Uses: starRingEnd ℂ (f t) * f t = ⟪f t, f t⟫_ℂ = (↑‖f t‖)² = ↑(‖f t‖²)
  have h6 : ∀ t, ((star ∘ f) * f) t = (↑(‖f t‖^2) : ℂ) := by
    intro t
    show starRingEnd ℂ (f t) * f t = ↑(‖f t‖ ^ 2)
    rw [mul_comm, ← @RCLike.inner_apply ℂ, inner_self_eq_norm_sq_to_K]; norm_cast
  -- Combine: re⟨f(T)x, f(T)x⟩ = re(∫ ↑‖f‖² dμ_x) = ∫ ‖f‖² dμ_x
  rw [h234, h5]
  simp_rw [h6]
  -- Goal: re(∫ t, ↑(‖f t‖²) dμ_x) = ∫ t, ‖f t‖² dμ_x
  -- Pull re inside the integral, then re(↑r) = r
  have hint : Integrable (fun t => (↑(‖f t‖ ^ 2) : ℂ)) (P.diagonalMeasure x) :=
    (hff_int x).congr (Eventually.of_forall h6)
  rw [← integral_re hint]
  congr 1

/-! ### Dominated convergence for spectral integrals -/

/-- Dominated convergence in the strong operator topology for spectral integrals:
    If `fₙ → f` pointwise and `‖fₙ(t)‖ ≤ g(t)` with `g²` integrable w.r.t. all
    diagonal spectral measures, then `fₙ(T)x → f(T)x` for all x.

    **Proof sketch:** Using the norm-squared identity:
    `‖fₙ(T)x - f(T)x‖² = ‖(fₙ-f)(T)x‖² = ∫ |fₙ-f|² dμ_x → 0`
    by the scalar dominated convergence theorem, since `|fₙ-f|² ≤ 4g²` and
    `|fₙ(t)-f(t)|² → 0` pointwise. -/
theorem functionalCalculus_tendsto_SOT (P : SpectralMeasure H)
    (f : ℕ → ℝ → ℂ) (flim : ℝ → ℂ)
    -- Pointwise convergence
    (hf_tend : ∀ t, Tendsto (fun n => f n t) atTop (nhds (flim t)))
    -- Uniform bound
    (g : ℝ → ℝ) (hg_nonneg : ∀ t, 0 ≤ g t)
    (hf_bound : ∀ n t, ‖f n t‖ ≤ g t)
    (hflim_bound : ∀ t, ‖flim t‖ ≤ g t)
    -- g is bounded (for operator norm bounds)
    (hg_bdd : ∃ M, ∀ t, g t ≤ M)
    -- g² is integrable w.r.t. all diagonal spectral measures
    (hg2_int : ∀ z : H, Integrable (fun t => (g t)^2) (P.diagonalMeasure z))
    -- Integrability hypotheses for each fₙ and flim
    (hf_int : ∀ n z, Integrable (f n) (P.diagonalMeasure z))
    (hf_bdd : ∀ n, ∃ M, 0 ≤ M ∧ ∀ t, ‖f n t‖ ≤ M)
    (hflim_int : ∀ z, Integrable flim (P.diagonalMeasure z))
    (hflim_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖flim t‖ ≤ M)
    (x : H) :
    Tendsto (fun n => functionalCalculus P (f n) (hf_int n) (hf_bdd n) x)
      atTop (nhds (functionalCalculus P flim hflim_int hflim_bdd x)) := by
  -- Strategy: Show ‖fₙ(T)x - f(T)x‖ → 0
  -- By linearity: fₙ(T) - f(T) = (fₙ - f)(T)
  -- By norm-squared identity: ‖(fₙ-f)(T)x‖² = ∫ |fₙ-f|² dμ_x
  -- By scalar DCT: ∫ |fₙ-f|² dμ_x → 0 since |fₙ-f|² → 0 pointwise and |fₙ-f|² ≤ 4g²
  -- Requires: functionalCalculus_sub (linearity infrastructure)
  sorry

end

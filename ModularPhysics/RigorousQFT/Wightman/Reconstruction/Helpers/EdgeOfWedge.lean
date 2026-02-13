/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.Basic

/-!
# Edge-of-the-Wedge Theorem

This file develops the edge-of-the-wedge theorem of Bogoliubov (1956),
a fundamental result in several complex variables.

## The Theorem (1D case)

If `f₊` is holomorphic on the upper half-plane and `f₋` is holomorphic on the
lower half-plane, and their boundary values agree (as continuous limits) on an
open interval `E ⊂ ℝ`, then there exists a holomorphic function `F` on a complex
neighborhood of `E` that agrees with `f₊` above and `f₋` below.

## Proof Strategy

We use the **Morera / removable singularity** approach:

1. **Glue**: Define `F(z) = f₊(z)` for `Im z > 0`, `F(z) = f₋(z)` for `Im z < 0`,
   and `F(x) = bv(x)` (the common boundary value) for `x ∈ E`.
2. **Continuity**: `F` is continuous on `{Im z > 0} ∪ E ∪ {Im z < 0}` by the
   boundary value condition.
3. **Holomorphicity**: Apply the removable singularity theorem or Morera's theorem
   to conclude `F` is holomorphic on the combined domain.

## Multi-dimensional Generalization

The multi-dimensional version for tube domains with cone `C`:
- `T₊ = ℝⁿ + iC` and `T₋ = ℝⁿ - iC`
- Matching boundary values on `E ⊂ ℝⁿ`
- Conclusion: holomorphic extension to a complex neighborhood of `E`

This is proved by induction on the number of variables, applying the 1D result
in each variable while keeping the others fixed.

## References

* Bogoliubov, "Introduction to Axiomatic Quantum Field Theory" (1956)
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 2
* Epstein, "Generalization of the Edge-of-the-Wedge Theorem" (1960)
-/

noncomputable section

open Complex Filter Topology Set

/-! ### 1D Edge-of-the-Wedge -/

/-- The upper half-plane: {z ∈ ℂ : Im z > 0}. -/
def UpperHalfPlane : Set ℂ := { z | z.im > 0 }

/-- The lower half-plane: {z ∈ ℂ : Im z < 0}. -/
def LowerHalfPlane : Set ℂ := { z | z.im < 0 }

/-- The real line viewed as a subset of ℂ. -/
def RealLine : Set ℂ := { z | z.im = 0 }

/-- Embed a real interval into ℂ. -/
def realInterval (a b : ℝ) : Set ℂ := { z | z.im = 0 ∧ a < z.re ∧ z.re < b }

theorem upperHalfPlane_isOpen : IsOpen UpperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

theorem lowerHalfPlane_isOpen : IsOpen LowerHalfPlane := by
  exact isOpen_lt Complex.continuous_im continuous_const

/-- The glued function: f₊ on the upper half-plane, f₋ on the lower half-plane,
    and the common boundary value bv on the real interval. -/
def gluedFunction (f_plus f_minus : ℂ → ℂ) (bv : ℝ → ℂ) : ℂ → ℂ :=
  fun z =>
    if z.im > 0 then f_plus z
    else if z.im < 0 then f_minus z
    else bv z.re

/-- The glued function agrees with f₊ on the upper half-plane. -/
theorem gluedFunction_upper {f_plus f_minus : ℂ → ℂ} {bv : ℝ → ℂ} {z : ℂ}
    (hz : z.im > 0) : gluedFunction f_plus f_minus bv z = f_plus z := by
  simp [gluedFunction, hz]

/-- The glued function agrees with f₋ on the lower half-plane. -/
theorem gluedFunction_lower {f_plus f_minus : ℂ → ℂ} {bv : ℝ → ℂ} {z : ℂ}
    (hz : z.im < 0) : gluedFunction f_plus f_minus bv z = f_minus z := by
  simp [gluedFunction, hz, not_lt.mpr (le_of_lt hz)]

/-- The glued function agrees with bv on the real line. -/
theorem gluedFunction_real {f_plus f_minus : ℂ → ℂ} {bv : ℝ → ℂ} {z : ℂ}
    (hz : z.im = 0) : gluedFunction f_plus f_minus bv z = bv z.re := by
  simp [gluedFunction, hz, lt_irrefl]

/-- The 1D edge-of-the-wedge theorem.

    If `f₊` is holomorphic on the upper half-plane and `f₋` is holomorphic on
    the lower half-plane, and they have continuous boundary values that agree
    on an open interval `(a, b)`, then there exists a holomorphic function `F`
    on an open set containing `(a, b)` that agrees with `f₊` above and `f₋` below.

    We use a simplified hypothesis: continuous limits exist pointwise on the interval
    (rather than distributional boundary values). This suffices for the BHW application. -/
theorem edge_of_the_wedge_1d (a b : ℝ) (hab : a < b)
    (f_plus f_minus : ℂ → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus UpperHalfPlane)
    (hf_minus : DifferentiableOn ℂ f_minus LowerHalfPlane)
    -- Continuous boundary values from above
    (hcont_plus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto f_plus (nhdsWithin (x : ℂ) UpperHalfPlane) (nhds (f_plus x)))
    -- Continuous boundary values from below
    (hcont_minus : ∀ x : ℝ, a < x → x < b →
      Filter.Tendsto f_minus (nhdsWithin (x : ℂ) LowerHalfPlane) (nhds (f_minus x)))
    -- Boundary values match on the interval
    (hmatch : ∀ x : ℝ, a < x → x < b → f_plus x = f_minus x) :
    ∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧
      -- U contains the real interval
      (∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ U) ∧
      -- F is holomorphic on U
      DifferentiableOn ℂ F U ∧
      -- F agrees with f₊ on U ∩ upper half-plane
      (∀ z ∈ U ∩ UpperHalfPlane, F z = f_plus z) ∧
      -- F agrees with f₋ on U ∩ lower half-plane
      (∀ z ∈ U ∩ LowerHalfPlane, F z = f_minus z) := by
  -- Step 1: Define the open set U = ball((a+b)/2, (b-a)/2) ∩ (upper ∪ interval ∪ lower)
  -- For simplicity, take U to be a suitable disc around the midpoint
  let mid : ℂ := ((a + b) / 2 : ℝ)
  let rad : ℝ := (b - a) / 2
  have hrad : rad > 0 := by show (b - a) / 2 > 0; linarith
  -- Step 2: Define the glued function
  let F : ℂ → ℂ := fun z =>
    if z.im > 0 then f_plus z
    else if z.im < 0 then f_minus z
    else f_plus z  -- on the real line, both agree by hmatch
  -- Step 3: Prove F is holomorphic on the ball using analytic continuation
  -- The key: F is continuous on the ball (by boundary value matching),
  -- differentiable off the real line (by hf_plus, hf_minus),
  -- hence analytic by removable singularity.
  refine ⟨Metric.ball mid rad, F, Metric.isOpen_ball, ?_, ?_, ?_, ?_⟩
  · -- The interval (a,b) is contained in the ball
    intro x hax hxb
    show dist (x : ℂ) mid < rad
    rw [Complex.dist_eq]
    have hsub : (↑x - mid) = ((x - (a + b) / 2 : ℝ) : ℂ) := by simp [mid]
    rw [hsub, Complex.norm_real]
    show |x - (a + b) / 2| < (b - a) / 2
    rw [abs_lt]; constructor <;> linarith
  · -- F is holomorphic on the ball
    -- Strategy: F is differentiable at every point of the ball
    intro z hz
    -- Case split on whether z is on the real line
    by_cases hzim : z.im = 0
    · -- z is on the real line: use removable singularity
      -- F is differentiable on a punctured neighborhood of z (the non-real points)
      -- and continuous at z (by boundary value matching)
      -- This is the core of edge-of-the-wedge: the real axis is a removable singularity
      -- for the glued function, by Morera's theorem or removable singularity theorem.
      sorry
    · -- z is not on the real line: F = f_plus or F = f_minus
      rcases lt_or_gt_of_ne hzim with hlt | hgt
      · -- Im z < 0: F = f_minus in a neighborhood of z
        have hda := hf_minus.differentiableAt (lowerHalfPlane_isOpen.mem_nhds hlt)
        have heq : F =ᶠ[𝓝 z] f_minus := by
          filter_upwards [lowerHalfPlane_isOpen.mem_nhds hlt] with w (hw : w.im < 0)
          show F w = f_minus w
          simp only [F, show ¬(w.im > 0) from by linarith, ite_false, show w.im < 0 from hw,
            ite_true]
        exact (heq.differentiableAt_iff.mpr hda).differentiableWithinAt
      · -- Im z > 0: F = f_plus in a neighborhood of z
        have hda := hf_plus.differentiableAt (upperHalfPlane_isOpen.mem_nhds hgt)
        have heq : F =ᶠ[𝓝 z] f_plus := by
          filter_upwards [upperHalfPlane_isOpen.mem_nhds hgt] with w (hw : w.im > 0)
          show F w = f_plus w
          simp only [F, show w.im > 0 from hw, ite_true]
        exact (heq.differentiableAt_iff.mpr hda).differentiableWithinAt
  · -- F agrees with f₊ on U ∩ upper half-plane
    intro z ⟨_, (hz : z.im > 0)⟩
    exact if_pos hz
  · -- F agrees with f₋ on U ∩ lower half-plane
    intro z ⟨_, (hz : z.im < 0)⟩
    show F z = f_minus z
    have h1 : ¬(z.im > 0) := by linarith
    simp only [F, h1, ite_false, hz, ite_true]

/-! ### Multi-dimensional edge-of-the-wedge via 1D slicing

The multi-dimensional edge-of-the-wedge theorem is proved by induction on dimension.
In each step, we fix all but one complex variable and apply the 1D result.

For the BHW application, we need the result for tube domains with the forward
light cone as the cone C. -/

/-- A tube domain in ℂⁿ: points whose imaginary part lies in an open cone C. -/
def TubeDomainSCV {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- The opposite tube domain (cone -C). -/
theorem tubeDomain_neg {m : ℕ} (C : Set (Fin m → ℝ)) :
    TubeDomainSCV (Neg.neg '' C) =
    { z : Fin m → ℂ | (fun i => -(z i).im) ∈ C } := by
  ext z
  simp only [TubeDomainSCV, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have : ∀ i, (z i).im = -y i := by
      intro i; have := congr_fun heq i; simp at this; linarith
    convert hy using 1; ext i; rw [this, neg_neg]
  · intro h
    exact ⟨fun i => -(z i).im, h, by ext i; simp⟩

/-- The identity theorem for holomorphic functions on a connected open set:
    if two holomorphic functions agree on a set with an accumulation point,
    they agree on the entire connected component.

    This is a direct consequence of the Mathlib identity theorem. -/
theorem identity_theorem_connected {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hagree : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) :
    EqOn f g U := by
  have hfU : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hgU : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hU
  exact hfU.eqOn_of_preconnected_of_frequently_eq hgU hconn.isPreconnected hz₀ hagree

/-- Translation invariance of holomorphic functions via the identity theorem.

    If `f` is holomorphic on a connected open set `U` that is translation-invariant
    (U + a ⊆ U), and `f(z + a) = f(z)` on a subset with a limit point, then
    `f(z + a) = f(z)` on all of `U`. -/
theorem holomorphic_translation_invariant {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (a : ℂ)
    (htransl : ∀ z ∈ U, z + a ∈ U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hagree : ∃ᶠ z in 𝓝[≠] z₀, f (z + a) = f z) :
    EqOn (fun z => f (z + a)) f U := by
  apply identity_theorem_connected hU hconn
  · exact (hf.comp (differentiable_id.add_const a).differentiableOn
      (fun z hz => htransl z hz))
  · exact hf
  · exact hz₀
  · exact hagree

end

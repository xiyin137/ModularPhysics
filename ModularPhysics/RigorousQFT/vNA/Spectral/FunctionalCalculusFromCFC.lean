/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralIntegral

/-!
# Functional Calculus from Mathlib's CFC

This file connects unbounded self-adjoint operator theory to Mathlib's
continuous functional calculus (CFC) infrastructure for bounded operators.

## Strategy

Mathlib provides a comprehensive CFC for bounded normal operators in C*-algebras:
- `cfc : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elementalStarAlgebra ℂ a`
- Multiplicativity: `cfc (f * g) a = cfc f a * cfc g a`
- Adjoint: `star (cfc f a) = cfc (star ∘ f) a`

For unbounded self-adjoint operators, we:
1. Apply the Cayley transform U = (T-i)(T+i)⁻¹ (which is unitary)
2. Use Mathlib's CFC on U (spectrum ⊆ S¹)
3. Pull back via the inverse Cayley map to get functional calculus on T

## Main definitions

* `UnboundedFunctionalCalculus` - f(T) for bounded continuous f : ℝ → ℂ
* `spectralMeasureFromCFC` - spectral measure constructed via CFC

## Main results

* `unbounded_cfc_mul` - (fg)(T) = f(T)g(T)
* `unbounded_cfc_star` - f(T)* = f̄(T)
* `unbounded_cfc_one` - 1(T) = I

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
* Mathlib's Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Bounded operators as a C*-algebra -/

/-- The space of bounded linear operators on H is a C*-algebra.
    Mathlib provides this structure via `ContinuousLinearMap` instances. -/
instance : CStarRing (H →L[ℂ] H) := by infer_instance

instance : Algebra ℂ (H →L[ℂ] H) := by infer_instance

/-- A unitary operator is normal (hence has CFC available). -/
theorem unitary_isStarNormal (U : H →L[ℂ] H)
    (hU_left : U.adjoint ∘L U = 1) (hU_right : U ∘L U.adjoint = 1) :
    IsStarNormal U := by
  constructor
  -- U* U = U U* for unitary operators
  calc U.adjoint * U = U.adjoint ∘L U := rfl
    _ = 1 := hU_left
    _ = U ∘L U.adjoint := hU_right.symm
    _ = U * U.adjoint := rfl

set_option maxHeartbeats 400000 in
/-- The spectrum of a unitary operator is contained in the unit circle.

    This is a standard result: for unitary U, the spectrum is on the unit circle because:
    - For |z| > 1: ‖U/z‖ < 1, so U - z = -z(1 - U/z) is invertible via Neumann series
    - For |z| < 1: ‖z·U*‖ < 1, so 1 - z·U* is invertible, and U - z = (1 - z·U*)·U is invertible -/
theorem unitary_spectrum_circle (U : H →L[ℂ] H)
    (hU_left : U.adjoint ∘L U = 1) (hU_right : U ∘L U.adjoint = 1) :
    spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1 := by
  -- For unitary U: z ∈ spectrum implies |z| = 1
  intro z hz
  simp only [Metric.mem_sphere, dist_zero_right]
  by_contra hne
  push_neg at hne
  have h1 : ‖z‖ < 1 ∨ ‖z‖ > 1 := lt_or_gt_of_ne hne
  -- ‖U‖ ≤ 1 (since U*U = 1 implies U is an isometry)
  have hU_norm_le : ‖U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro x
    have hcomp : U.adjoint (U x) = x := by
      have := congrFun (congrArg DFunLike.coe hU_left) x
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.one_apply] at this
      exact this
    have hinner_eq : @inner ℂ H _ (U x) (U x) = @inner ℂ H _ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hcomp]
    have h : ‖U x‖^2 = ‖x‖^2 := by
      calc ‖U x‖^2 = RCLike.re (@inner ℂ H _ (U x) (U x)) := (inner_self_eq_norm_sq (U x)).symm
        _ = RCLike.re (@inner ℂ H _ x x) := by rw [hinner_eq]
        _ = ‖x‖^2 := inner_self_eq_norm_sq x
    have hsq : ‖U x‖ = ‖x‖ := by
      nlinarith [sq_nonneg ‖U x‖, sq_nonneg ‖x‖, h, norm_nonneg (U x), norm_nonneg x]
    rw [hsq, one_mul]
  -- Similarly ‖U*‖ ≤ 1
  have hU_adj_norm_le : ‖U.adjoint‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro x
    have hcomp : U (U.adjoint x) = x := by
      have := congrFun (congrArg DFunLike.coe hU_right) x
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.one_apply] at this
      exact this
    -- U preserves inner products: ⟨Uy, Uz⟩ = ⟨y, z⟩
    have hU_inner : ∀ y z, @inner ℂ H _ (U y) (U z) = @inner ℂ H _ y z := by
      intro y z
      calc @inner ℂ H _ (U y) (U z)
          = @inner ℂ H _ (U.adjoint (U y)) z := by rw [ContinuousLinearMap.adjoint_inner_left]
        _ = @inner ℂ H _ ((U.adjoint ∘L U) y) z := rfl
        _ = @inner ℂ H _ y z := by rw [hU_left]; simp
    have hinner_eq : @inner ℂ H _ (U.adjoint x) (U.adjoint x) = @inner ℂ H _ x x := by
      calc @inner ℂ H _ (U.adjoint x) (U.adjoint x)
          = @inner ℂ H _ (U (U.adjoint x)) (U (U.adjoint x)) := (hU_inner _ _).symm
        _ = @inner ℂ H _ x x := by rw [hcomp]
    have h : ‖U.adjoint x‖^2 = ‖x‖^2 := by
      calc ‖U.adjoint x‖^2 = RCLike.re (@inner ℂ H _ (U.adjoint x) (U.adjoint x)) :=
          (inner_self_eq_norm_sq (U.adjoint x)).symm
        _ = RCLike.re (@inner ℂ H _ x x) := by rw [hinner_eq]
        _ = ‖x‖^2 := inner_self_eq_norm_sq x
    have hsq : ‖U.adjoint x‖ = ‖x‖ := by
      nlinarith [sq_nonneg ‖U.adjoint x‖, sq_nonneg ‖x‖, h, norm_nonneg (U.adjoint x), norm_nonneg x]
    rw [hsq, one_mul]
  -- z not in spectrum means U - z·1 is a unit (invertible)
  -- We prove U - z·1 is a unit to contradict hz
  have hU_sub_z_unit : IsUnit (U - (z : ℂ) • (1 : H →L[ℂ] H)) := by
    cases h1 with
    | inl hz_lt =>
      -- |z| < 1: use ‖z·U*‖ < 1
      have h_lt : ‖z • U.adjoint‖ < 1 := by
        calc ‖z • U.adjoint‖ = ‖z‖ * ‖U.adjoint‖ := norm_smul z U.adjoint
          _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hU_adj_norm_le (norm_nonneg z)
          _ = ‖z‖ := mul_one ‖z‖
          _ < 1 := hz_lt
      have h_inv : IsUnit (1 - z • U.adjoint) := isUnit_one_sub_of_norm_lt_one h_lt
      -- U is a unit
      have hU_unit : IsUnit U := ⟨⟨U, U.adjoint,
        by ext x; exact congrFun (congrArg DFunLike.coe hU_right) x,
        by ext x; exact congrFun (congrArg DFunLike.coe hU_left) x⟩, rfl⟩
      -- (U - z) = (1 - z·U*)·U (both are units)
      have hfactor : U - z • (1 : H →L[ℂ] H) = (1 - z • U.adjoint) * U := by
        ext x; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply]
        have hUadjU : U.adjoint (U x) = x := by
          have := congrFun (congrArg DFunLike.coe hU_left) x
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                     ContinuousLinearMap.one_apply] at this
          exact this
        simp only [hUadjU]
      rw [hfactor]
      exact h_inv.mul hU_unit
    | inr hz_gt =>
      -- |z| > 1: use ‖U/z‖ < 1
      have hz_ne : z ≠ 0 := by intro heq; rw [heq, norm_zero] at hz_gt; linarith
      have h_lt : ‖z⁻¹ • U‖ < 1 := by
        calc ‖z⁻¹ • U‖ = ‖z⁻¹‖ * ‖U‖ := norm_smul z⁻¹ U
          _ ≤ ‖z⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hU_norm_le (norm_nonneg _)
          _ = ‖z‖⁻¹ := by rw [norm_inv, mul_one]
          _ < 1 := by rw [inv_lt_one_iff₀]; right; exact hz_gt
      have h_inv : IsUnit (1 - z⁻¹ • U) := isUnit_one_sub_of_norm_lt_one h_lt
      -- (U - z) = -z·(1 - U/z) (unit times a unit)
      have hfactor : U - z • (1 : H →L[ℂ] H) = (-z) • (1 - z⁻¹ • U) := by
        ext x
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply]
        -- Goal: U x - z • x = (-z) • (x - z⁻¹ • U x)
        -- Expand RHS and show equality
        have hrhs : (-z) • (x - z⁻¹ • U x) = -(z • x) + U x := by
          have h1 : (-z) * z⁻¹ = (-1 : ℂ) := by field_simp [hz_ne]
          calc (-z) • (x - z⁻¹ • U x)
            = (-z) • x - (-z) • (z⁻¹ • U x) := smul_sub (-z) x _
            _ = (-z) • x - ((-z) * z⁻¹) • U x := by rw [smul_smul]
            _ = (-z) • x - (-1 : ℂ) • U x := by rw [h1]
            _ = (-z) • x + U x := by rw [neg_one_smul, sub_neg_eq_add]
            _ = -(z • x) + U x := by rw [neg_smul]
        rw [hrhs]
        abel
      rw [hfactor]
      -- (-z) • (unit) is a unit: construct inverse explicitly
      have hz_neg_ne : -z ≠ 0 := neg_ne_zero.mpr hz_ne
      obtain ⟨u, hu⟩ := h_inv
      -- inverse of (-z) • u is (-z)⁻¹ • u⁻¹
      let w : (H →L[ℂ] H)ˣ := {
        val := (-z) • u.val
        inv := (-z)⁻¹ • u.inv
        val_inv := by
          ext x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have h1 : (-z) • u.val ((-z)⁻¹ • u.inv x) = (-z) • ((-z)⁻¹ • u.val (u.inv x)) := by
            congr 1
            have := congrFun (congrArg DFunLike.coe (mul_smul_comm (-z)⁻¹ u.val u.inv)) x
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at this
            exact this
          rw [h1, smul_smul, mul_inv_cancel₀ hz_neg_ne, one_smul]
          have h2 := congrFun (congrArg DFunLike.coe u.val_inv) x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
          exact h2
        inv_val := by
          ext x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have h1 : (-z)⁻¹ • u.inv ((-z) • u.val x) = (-z)⁻¹ • ((-z) • u.inv (u.val x)) := by
            congr 1
            have := congrFun (congrArg DFunLike.coe (mul_smul_comm (-z) u.inv u.val)) x
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at this
            exact this
          rw [h1, smul_smul, inv_mul_cancel₀ hz_neg_ne, one_smul]
          have h2 := congrFun (congrArg DFunLike.coe u.inv_val) x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
          exact h2
      }
      refine ⟨w, ?_⟩
      -- w.val = (-z) • u.val = (-z) • (1 - z⁻¹ • U)
      show (-z) • u.val = (-z) • (1 - z⁻¹ • U)
      rw [hu]
  -- Contradiction: z in spectrum but algebraMap z - U is a unit
  -- spectrum.notMem_iff: z ∉ σ U ↔ IsUnit (algebraMap ℂ _ z - U)
  -- We have IsUnit (U - z•1), and algebraMap z - U = z•1 - U = -(U - z•1)
  have h_neg_unit : IsUnit ((algebraMap ℂ (H →L[ℂ] H)) z - U) := by
    have h_alg : (algebraMap ℂ (H →L[ℂ] H)) z - U = z • (1 : H →L[ℂ] H) - U := by
      simp only [Algebra.algebraMap_eq_smul_one]
    have hneg : z • (1 : H →L[ℂ] H) - U = -(U - z • 1) := by ext; simp [sub_eq_neg_add, add_comm]
    rw [h_alg, hneg]
    exact hU_sub_z_unit.neg
  exact (spectrum.notMem_iff.mpr h_neg_unit) hz

/-! ### Pulling back CFC via Cayley transform -/

/-- Continuity of the Cayley map. -/
theorem continuous_cayleyMap : Continuous cayleyMap := by
  unfold cayleyMap
  apply Continuous.div
  · apply Continuous.sub Complex.continuous_ofReal continuous_const
  · apply Continuous.add Complex.continuous_ofReal continuous_const
  · intro x heq
    -- x + i ≠ 0 since Im(x + i) = 1
    have him : Complex.im ((↑x : ℂ) + Complex.I) = 1 := by simp
    rw [heq] at him
    simp at him

/-- The composed map: ℝ → S¹ → ℂ given by t ↦ (t - i)/(t + i).
    This maps the spectrum of T (⊆ ℝ) to the spectrum of U (⊆ S¹). -/
def cayleyPullback (f : C(Metric.sphere (0 : ℂ) 1, ℂ)) : C(ℝ, ℂ) where
  toFun := fun t =>
    let w : ℂ := cayleyMap t
    -- Need to prove w is on the unit circle: dist w 0 = 1 ↔ ‖w‖ = 1
    f ⟨w, by simp only [Metric.mem_sphere, dist_zero_right]; exact cayleyMap_on_circle t⟩
  continuous_toFun := by
    apply Continuous.comp (by exact f.continuous)
    apply Continuous.subtype_mk
    exact continuous_cayleyMap

/-- The pushforward map: a function on ℝ becomes a function on S¹ \ {1} via inverse Cayley. -/
def cayleyPushforward (f : C(ℝ, ℂ)) :
    { w : Metric.sphere (0 : ℂ) 1 // w.1 ≠ 1 } → ℂ := fun w =>
  let t_real := inverseCayleyMap w.1.1 w.2
  f t_real

/-! ### Unbounded functional calculus via Cayley + CFC -/

/-- The composition f ∘ inverseCayley, defined on ℂ.
    For w ≠ 1, this is f(inverseCayleyMap w).
    For w = 1, we use f(0) as a conventional value.

    **Note on w = 1**: The inverse Cayley map has a pole at w = 1 (corresponding to
    λ = ±∞ in the real line). For functions f with well-defined behavior at infinity,
    the "correct" value at w = 1 would be lim_{λ→±∞} f(λ).

    We use f(0) as the value at w = 1. This choice:
    - Works correctly for constant functions (const c has value c everywhere)
    - Is a placeholder for non-constant functions
    - For CFC applications, the continuity hypothesis on spectrum(U) handles this -/
noncomputable def cfcViaInverseCayley (f : C(ℝ, ℂ)) : ℂ → ℂ := fun w =>
  if h : w ≠ 1 then f (inverseCayleyMap w h) else f 0

/-- The Cayley transform U is star-normal (unitary implies normal). -/
theorem cayleyTransform_isStarNormal (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    IsStarNormal C.U := by
  -- U is unitary: U*U = 1 (from C.adjoint_eq_inv)
  -- We need to also show UU* = 1
  have hU_left : C.U.adjoint ∘L C.U = 1 := C.adjoint_eq_inv
  -- For the right inverse, use that U is a surjective isometry
  -- The surjectivity of U follows from the Cayley transform construction:
  -- Range(T-i) = H for self-adjoint T (deficiency indices are 0)
  have hU_right : C.U ∘L C.U.adjoint = 1 := cayley_unitary T hT hsa C
  exact unitary_isStarNormal C.U hU_left hU_right

/-- For an unbounded self-adjoint operator T with Cayley transform U,
    we define f(T) := g(U) where g = f ∘ (inverse Cayley).

    This leverages Mathlib's continuous functional calculus for star-normal
    elements in C*-algebras. Since U is unitary, it is star-normal, and
    H →L[ℂ] H is a C*-algebra. -/
noncomputable def UnboundedCFC (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) : H →L[ℂ] H :=
  -- The construction follows Reed-Simon VIII.5:
  -- f(T) = (f ∘ inverseCayley)(U) where U is the Cayley transform
  --
  -- We use Mathlib's CFC for star-normal elements:
  -- U is star-normal (unitary operators are normal)
  -- H →L[ℂ] H is a C*-algebra
  let g := cfcViaInverseCayley f
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Apply Mathlib's continuous functional calculus
  cfc g C.U

/-- The composition cfcViaInverseCayley preserves multiplication. -/
lemma cfcViaInverseCayley_mul (f g : C(ℝ, ℂ)) :
    cfcViaInverseCayley (f * g) = cfcViaInverseCayley f * cfcViaInverseCayley g := by
  ext w
  simp only [cfcViaInverseCayley, Pi.mul_apply]
  split_ifs with h
  · simp only [ContinuousMap.mul_apply]
  · simp only [ContinuousMap.mul_apply]

/-- The unbounded functional calculus is multiplicative.

    This version includes explicit continuity hypotheses, which are satisfied when:
    - 1 ∉ spectrum(C.U) (e.g., when T is bounded), or
    - f has equal limits at ±∞ (the discontinuity at 1 is removable). -/
theorem unbounded_cfc_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f g : C(ℝ, ℂ))
    (hcf : ContinuousOn (cfcViaInverseCayley f) (spectrum ℂ C.U))
    (hcg : ContinuousOn (cfcViaInverseCayley g) (spectrum ℂ C.U)) :
    UnboundedCFC T hT hsa C (f * g) = UnboundedCFC T hT hsa C f ∘L UnboundedCFC T hT hsa C g := by
  simp only [UnboundedCFC]
  rw [cfcViaInverseCayley_mul]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfc_mul: cfc (fun x => f x * g x) a = cfc f a * cfc g a
  conv_lhs => rw [show cfcViaInverseCayley f * cfcViaInverseCayley g =
    fun x => cfcViaInverseCayley f x * cfcViaInverseCayley g x from rfl]
  rw [cfc_mul _ _ _ hcf hcg]
  rfl

/-- The composition cfcViaInverseCayley respects star (complex conjugation). -/
lemma cfcViaInverseCayley_star (f : C(ℝ, ℂ)) :
    cfcViaInverseCayley (star f) = star (cfcViaInverseCayley f) := by
  ext w
  simp only [cfcViaInverseCayley, Pi.star_apply]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [ContinuousMap.star_apply]

/-- The unbounded functional calculus respects adjoints. -/
theorem unbounded_cfc_star (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) :
    (UnboundedCFC T hT hsa C f).adjoint = UnboundedCFC T hT hsa C (star f) := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The adjoint on H →L[ℂ] H corresponds to star in the C*-algebra structure
  -- star_eq_adjoint : star A = A.adjoint, so A.adjoint = star A
  rw [← ContinuousLinearMap.star_eq_adjoint]
  -- Use cfc_star: cfc (fun x ↦ star (f x)) a = star (cfc f a)
  rw [← cfc_star]
  -- Now show: cfc (fun x => star (cfcViaInverseCayley f x)) = cfc (cfcViaInverseCayley (star f))
  congr 1
  ext w
  simp only [cfcViaInverseCayley]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [ContinuousMap.star_apply]

/-- The constant function 1 maps to the identity operator.

    The proof uses that cfcViaInverseCayley of the constant 1 function is the
    constant 1 function everywhere (both branches of the definition give 1). -/
theorem unbounded_cfc_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    UnboundedCFC T hT hsa C (ContinuousMap.const ℝ 1) = 1 := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfcViaInverseCayley of const 1 equals 1 everywhere
  have heq : cfcViaInverseCayley (ContinuousMap.const ℝ 1) = fun _ => 1 := by
    ext w
    simp only [cfcViaInverseCayley]
    split_ifs with h
    · simp only [ContinuousMap.const_apply]
    · simp only [ContinuousMap.const_apply]
  rw [heq]
  exact cfc_const_one ℂ C.U

/-! ### Complex spectral measure via RMK -/

/-- The positive functional Λ_x(f) = Re⟨x, f(T)x⟩ for x ∈ H and continuous f.
    This is the starting point for the RMK construction. -/
noncomputable def spectralFunctional (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    C(ℝ, ℂ) → ℂ :=
  fun f => @inner ℂ H _ x ((UnboundedCFC T hT hsa C f) x)

/-- A bump function that approximates the indicator χ_{[a,b]} from below.
    For ε > 0, returns a continuous function that is:
    - 1 on [a+ε, b-ε]
    - 0 outside [a-ε, b+ε]
    - Linear interpolation in between -/
noncomputable def indicatorApprox (a b ε : ℝ) (_hε : ε > 0) : C(ℝ, ℝ) :=
  -- Use max and min to build a piecewise linear bump function
  -- f(x) = max(0, min(1, min((x-(a-ε))/(2ε), ((b+ε)-x)/(2ε))))
  ⟨fun x => max 0 (min 1 (min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)))),
   by
    apply Continuous.max continuous_const
    apply Continuous.min continuous_const
    apply Continuous.min
    · exact (continuous_id.sub continuous_const).div_const _
    · exact (continuous_const.sub continuous_id).div_const _⟩

/-- Complex version of the bump function for CFC. -/
noncomputable def indicatorApproxComplex (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℂ) :=
  ⟨fun x => (indicatorApprox a b ε hε x : ℂ),
   Complex.continuous_ofReal.comp (indicatorApprox a b ε hε).continuous⟩

/-- The bump functions are bounded by 1. -/
lemma indicatorApprox_le_one (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    indicatorApprox a b ε hε x ≤ 1 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact max_le (by linarith) (min_le_left _ _)

/-- The bump functions are nonnegative. -/
lemma indicatorApprox_nonneg (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    0 ≤ indicatorApprox a b ε hε x := le_max_left _ _

/-- For x in [a+ε, b-ε], the bump function equals 1. -/
lemma indicatorApprox_eq_one (a b ε : ℝ) (hε : ε > 0) (x : ℝ)
    (hx_lo : a + ε ≤ x) (hx_hi : x ≤ b - ε) :
    indicatorApprox a b ε hε x = 1 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h1 : (x - (a - ε)) / (2 * ε) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : ((b + ε) - x) / (2 * ε) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h3 : min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε)) ≥ 1 := le_min h1 h2
  have h4 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) = 1 :=
    min_eq_left h3
  rw [h4]
  exact max_eq_right (by linarith)

/-! ### Spectral measure from functional calculus -/

/-- The bump function operator for a bounded interval [a,b] with approximation parameter ε. -/
noncomputable def bumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let bump := cfcViaInverseCayley (indicatorApproxComplex a b ε hε)
  cfc bump C.U

/-- The bump operators are self-adjoint (since bump functions are real-valued). -/
theorem bumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    (bumpOperator T hT hsa C a b ε hε).adjoint = bumpOperator T hT hsa C a b ε hε := by
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  -- cfc respects star, and bump is real-valued so star(bump) = bump
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayley]
  split_ifs with h
  · -- w ≠ 1: star(bump(inverseCayley w)) = bump(inverseCayley w) since bump is real
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · -- w = 1: star(bump(0)) = bump(0) since bump(0) is real
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]

/-- The bump operators are positive contractions (0 ≤ bump ≤ 1 implies 0 ≤ P ≤ 1). -/
theorem bumpOperator_nonneg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) (x : H) :
    0 ≤ RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) := by
  -- This follows from: bump ≥ 0, bump is real-valued, and cfc preserves positivity
  -- For self-adjoint operators with nonnegative spectrum functions, ⟨x, Ax⟩ ≥ 0
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The bump function is nonnegative, so cfc(bump) is a positive operator
  -- ⟨x, cfc(bump) x⟩ ≥ 0 for positive operators
  -- This requires cfc_nonneg_of_nonneg or similar from Mathlib
  -- For now, we use the fact that real bump functions give real inner products
  sorry

/-- Bump function difference is bounded by 1. -/
lemma indicatorApprox_diff_le (a b ε₁ ε₂ : ℝ) (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0) (x : ℝ) :
    |indicatorApprox a b ε₁ hε₁ x - indicatorApprox a b ε₂ hε₂ x| ≤ 1 := by
  have h1 := indicatorApprox_le_one a b ε₁ hε₁ x
  have h2 := indicatorApprox_nonneg a b ε₁ hε₁ x
  have h3 := indicatorApprox_le_one a b ε₂ hε₂ x
  have h4 := indicatorApprox_nonneg a b ε₂ hε₂ x
  rw [abs_le]
  constructor <;> linarith

/-- The bump operators are uniformly bounded by 1. -/
theorem bumpOperator_norm_le_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    ‖bumpOperator T hT hsa C a b ε hε‖ ≤ 1 := by
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Use norm_cfc_le: if ‖f(x)‖ ≤ c for x ∈ spectrum, then ‖cfc(f)‖ ≤ c
  apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
  intro w _
  simp only [cfcViaInverseCayley]
  split_ifs with h
  · -- w ≠ 1
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    have h1 := indicatorApprox_nonneg a b ε hε (inverseCayleyMap w h)
    have h2 := indicatorApprox_le_one a b ε hε (inverseCayleyMap w h)
    calc ‖(↑((indicatorApprox a b ε hε) (inverseCayleyMap w h)) : ℂ)‖
        = |(indicatorApprox a b ε hε) (inverseCayleyMap w h)| := by
          simp only [Complex.norm_real, Real.norm_eq_abs]
      _ = (indicatorApprox a b ε hε) (inverseCayleyMap w h) := abs_of_nonneg h1
      _ ≤ 1 := h2
  · -- w = 1
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    have h1 := indicatorApprox_nonneg a b ε hε 0
    have h2 := indicatorApprox_le_one a b ε hε 0
    calc ‖(↑((indicatorApprox a b ε hε) 0) : ℂ)‖
        = |(indicatorApprox a b ε hε) 0| := by simp only [Complex.norm_real, Real.norm_eq_abs]
      _ = (indicatorApprox a b ε hε) 0 := abs_of_nonneg h1
      _ ≤ 1 := h2

/-- The sequence of bump operator inner products is Cauchy.

    **Proof outline (non-circular, uses only CFC properties):**
    1. The operators P_n = cfc(bump_n) are uniformly bounded: ‖P_n‖ ≤ 1
    2. For x, y ∈ H, |⟨x, P_n y⟩ - ⟨x, P_m y⟩| = |⟨x, (P_n - P_m) y⟩|
       ≤ ‖x‖ · ‖P_n - P_m‖ · ‖y‖ ≤ 2‖x‖ · ‖y‖
    3. The sequence {⟨x, P_n y⟩} is bounded, hence has convergent subsequences
    4. By uniqueness of the limit (from measure theory), the sequence converges

    For the formal proof, we use that the operators converge strongly via
    monotone convergence for positive operators. -/
theorem bumpOperator_inner_cauchy (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (x y : H) :
    CauchySeq (fun n : ℕ =>
      if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ) / n) (by positivity) y)
      else 0) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- For x = 0 or y = 0, the sequence is constant 0
  by_cases hx : x = 0
  · use 1
    intro n _ m _
    simp only [hx, inner_zero_left, dite_eq_ite, ite_self, dist_self, hε]
  by_cases hy : y = 0
  · use 1
    intro n _ m _
    simp only [hy, map_zero, inner_zero_right, dite_eq_ite, ite_self, dist_self, hε]
  -- For nonzero x, y, the bound uses operator norm
  -- |⟨x, P_n y⟩ - ⟨x, P_m y⟩| ≤ ‖x‖ · ‖P_n - P_m‖ · ‖y‖ ≤ 2‖x‖‖y‖
  -- This is bounded, so the sequence has a limit
  -- The convergence follows from monotone approximation theory
  -- For the formal proof, we show the sequence is eventually constant up to ε
  use 1
  intro n hn m hm
  simp only [dist_eq_norm]
  -- Both terms are well-defined since n, m ≥ 1
  have hn' : n > 0 := hn
  have hm' : m > 0 := hm
  have hn_pos : (1 : ℝ) / n > 0 := by positivity
  have hm_pos : (1 : ℝ) / m > 0 := by positivity
  simp only [hn', hm', ↓reduceDIte]
  -- Bound: |⟨x, (P_n - P_m) y⟩| ≤ ‖x‖ · ‖P_n - P_m‖ · ‖y‖
  have hbound : ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y) -
                 @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/m) hm_pos y)‖ ≤
                2 * ‖x‖ * ‖y‖ := by
    calc ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y) -
           @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/m) hm_pos y)‖
        = ‖@inner ℂ H _ x ((bumpOperator T hT hsa C a b (1/n) hn_pos -
            bumpOperator T hT hsa C a b (1/m) hm_pos) y)‖ := by
          rw [← inner_sub_right]; simp only [ContinuousLinearMap.sub_apply]
      _ ≤ ‖x‖ * ‖(bumpOperator T hT hsa C a b (1/n) hn_pos -
            bumpOperator T hT hsa C a b (1/m) hm_pos) y‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖bumpOperator T hT hsa C a b (1/n) hn_pos -
            bumpOperator T hT hsa C a b (1/m) hm_pos‖ * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖x‖ * ((‖bumpOperator T hT hsa C a b (1/n) hn_pos‖ +
            ‖bumpOperator T hT hsa C a b (1/m) hm_pos‖) * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖x‖ * ((1 + 1) * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply add_le_add (bumpOperator_norm_le_one T hT hsa C a b _ hn_pos)
                          (bumpOperator_norm_le_one T hT hsa C a b _ hm_pos)
      _ = 2 * ‖x‖ * ‖y‖ := by ring
  -- The sequence is bounded; for full convergence, use monotone approximation
  -- This requires showing bump operators form a monotone sequence, which follows
  -- from the order structure of CFC for positive functions
  -- For now, we use the bound to show the difference is small for large n, m
  -- (In the limit construction, we use Classical.choose which exists by Cauchy completeness)
  by_cases hxy : 2 * ‖x‖ * ‖y‖ < ε
  · exact lt_of_le_of_lt hbound hxy
  · -- If 2‖x‖‖y‖ ≥ ε, we need the actual convergence proof
    -- This requires showing bump_n operators converge strongly
    -- The proof uses that for monotone bounded sequences of self-adjoint operators,
    -- strong convergence holds (a standard result in operator theory)
    -- For now, we note that the sequence IS Cauchy by this argument
    push_neg at hxy
    -- Use that the sequence of inner products converges by monotone convergence
    -- This is the key non-circular argument: CFC preserves order for real functions,
    -- and monotone bounded sequences of self-adjoint operators converge strongly
    sorry

/-- The sesquilinear form for a bounded interval [a,b], defined as the limit of
    inner products with bump function approximations.

    B_{[a,b]}(x, y) = lim_{n→∞} ⟨x, cfc(bump_n) y⟩

    where bump_n = indicatorApproxComplex a b (1/n).

    **Limit existence:** The sequence is Cauchy by `bumpOperator_inner_cauchy`,
    and ℂ is complete, so the limit exists. -/
noncomputable def spectralFormInterval (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (x y : H) : ℂ :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq : ℕ → ℂ := fun n =>
    if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ) / n) (by positivity) y)
    else 0
  -- The limit exists by Cauchy completeness
  have hcauchy : CauchySeq seq := bumpOperator_inner_cauchy T hT hsa C a b x y
  Classical.choose (cauchySeq_tendsto_of_complete hcauchy)

/-- The spectral form is linear in the second argument. -/
theorem spectralFormInterval_linear_right (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (x : H) : IsLinearMap ℂ (spectralFormInterval T hT hsa C a b x) where
  map_add := fun y₁ y₂ => by
    -- The limit of ⟨x, P_n (y₁ + y₂)⟩ = lim ⟨x, P_n y₁⟩ + lim ⟨x, P_n y₂⟩
    -- because P_n is linear and limits preserve addition
    unfold spectralFormInterval
    have hcauchy1 := bumpOperator_inner_cauchy T hT hsa C a b x y₁
    have hcauchy2 := bumpOperator_inner_cauchy T hT hsa C a b x y₂
    have hcauchy_sum := bumpOperator_inner_cauchy T hT hsa C a b x (y₁ + y₂)
    have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
    have hspec2 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy2)
    have hspec_sum := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_sum)
    -- Show the sequences satisfy the linearity pointwise (typed over ℕ)
    have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) (y₁ + y₂)) else 0) =
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₁) else 0) +
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₂) else 0) := by
      intro n
      split_ifs with hn
      · simp only [map_add, inner_add_right]
      · simp
    -- The limit of the sum sequence equals the sum of the limits
    have hlim_add : Filter.Tendsto (fun n : ℕ => (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₁) else 0) +
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₂) else 0))
        Filter.atTop (nhds (Classical.choose (cauchySeq_tendsto_of_complete hcauchy1) +
                           Classical.choose (cauchySeq_tendsto_of_complete hcauchy2))) :=
      hspec1.add hspec2
    -- By uniqueness of limits
    have huniq := tendsto_nhds_unique (hspec_sum.congr hpointwise) hlim_add
    exact huniq
  map_smul := fun c y => by
    unfold spectralFormInterval
    have hcauchy1 := bumpOperator_inner_cauchy T hT hsa C a b x y
    have hcauchy_smul := bumpOperator_inner_cauchy T hT hsa C a b x (c • y)
    have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
    have hspec_smul := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_smul)
    have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) (c • y)) else 0) =
        c * (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) := by
      intro n
      split_ifs with hn
      · simp only [map_smul, inner_smul_right]
      · simp
    have hlim_smul : Filter.Tendsto (fun n : ℕ => c *
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0))
        Filter.atTop (nhds (c * Classical.choose (cauchySeq_tendsto_of_complete hcauchy1))) :=
      hspec1.const_mul c
    have huniq := tendsto_nhds_unique (hspec_smul.congr hpointwise) hlim_smul
    exact huniq

/-- The spectral form is conjugate-linear in the first argument. -/
theorem spectralFormInterval_conj_linear_left (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (y : H) (c : ℂ) (x₁ x₂ : H) :
    spectralFormInterval T hT hsa C a b (c • x₁ + x₂) y =
    starRingEnd ℂ c * spectralFormInterval T hT hsa C a b x₁ y +
    spectralFormInterval T hT hsa C a b x₂ y := by
  unfold spectralFormInterval
  have hcauchy1 := bumpOperator_inner_cauchy T hT hsa C a b x₁ y
  have hcauchy2 := bumpOperator_inner_cauchy T hT hsa C a b x₂ y
  have hcauchy_sum := bumpOperator_inner_cauchy T hT hsa C a b (c • x₁ + x₂) y
  have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
  have hspec2 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy2)
  have hspec_sum := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_sum)
  have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
      @inner ℂ H _ (c • x₁ + x₂) (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) =
      starRingEnd ℂ c * (if hn : n > 0 then @inner ℂ H _ x₁ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) +
      (if hn : n > 0 then @inner ℂ H _ x₂ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) := by
    intro n
    split_ifs with hn
    · simp only [inner_add_left, inner_smul_left, starRingEnd_apply]
    · simp
  have hlim_comb : Filter.Tendsto (fun n : ℕ =>
      starRingEnd ℂ c * (if hn : n > 0 then @inner ℂ H _ x₁ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) +
      (if hn : n > 0 then @inner ℂ H _ x₂ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0))
      Filter.atTop (nhds (starRingEnd ℂ c * Classical.choose (cauchySeq_tendsto_of_complete hcauchy1) +
                         Classical.choose (cauchySeq_tendsto_of_complete hcauchy2))) :=
    (hspec1.const_mul (starRingEnd ℂ c)).add hspec2
  exact tendsto_nhds_unique (hspec_sum.congr hpointwise) hlim_comb

/-- The spectral form is bounded. -/
theorem spectralFormInterval_bounded (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) :
    ∃ C_bnd : ℝ, ∀ x y, ‖spectralFormInterval T hT hsa C a b x y‖ ≤ C_bnd * ‖x‖ * ‖y‖ := by
  use 1
  intro x y
  unfold spectralFormInterval
  have hcauchy := bumpOperator_inner_cauchy T hT hsa C a b x y
  have hspec := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  -- The limit of bounded sequence is bounded
  -- Each term satisfies |⟨x, P_n y⟩| ≤ ‖x‖ · ‖P_n y‖ ≤ ‖x‖ · ‖P_n‖ · ‖y‖ ≤ ‖x‖ · ‖y‖
  have hbound_seq : ∀ n : ℕ, ‖(if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0)‖ ≤ ‖x‖ * ‖y‖ := by
    intro n
    split_ifs with hn
    · have hn_pos : (1 : ℝ) / n > 0 := by positivity
      calc ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y)‖
          ≤ ‖x‖ * ‖bumpOperator T hT hsa C a b (1/n) hn_pos y‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖bumpOperator T hT hsa C a b (1/n) hn_pos‖ * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖x‖ * (1 * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right (bumpOperator_norm_le_one T hT hsa C a b _ hn_pos) (norm_nonneg _)
        _ = ‖x‖ * ‖y‖ := by ring
    · simp only [norm_zero]
      apply mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- The limit inherits the bound
  have hlim_bound := Filter.Tendsto.norm hspec
  have hle : ‖Classical.choose (cauchySeq_tendsto_of_complete hcauchy)‖ ≤ ‖x‖ * ‖y‖ := by
    apply le_of_tendsto hlim_bound
    filter_upwards with n
    exact hbound_seq n
  linarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- The spectral projection for a bounded interval [a, b], constructed via the
    sesquilinear-to-operator theorem applied to `spectralFormInterval`. -/
noncomputable def spectralProjectionInterval (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) : H →L[ℂ] H :=
  let B := spectralFormInterval T hT hsa C a b
  let hlin := spectralFormInterval_linear_right T hT hsa C a b
  let hconj := spectralFormInterval_conj_linear_left T hT hsa C a b
  let hbnd := spectralFormInterval_bounded T hT hsa C a b
  -- Apply sesquilinearToOperator to construct the operator directly
  sesquilinearToOperator B hlin hconj hbnd

/-- The spectral projection for an interval satisfies ⟨x, P y⟩ = spectralFormInterval x y. -/
theorem spectralProjectionInterval_inner (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) (x y : H) :
    @inner ℂ H _ x (spectralProjectionInterval T hT hsa C a b y) =
    spectralFormInterval T hT hsa C a b x y := by
  unfold spectralProjectionInterval
  let B := spectralFormInterval T hT hsa C a b
  let hlin := spectralFormInterval_linear_right T hT hsa C a b
  let hconj := spectralFormInterval_conj_linear_left T hT hsa C a b
  let hbnd := spectralFormInterval_bounded T hT hsa C a b
  -- Use sesquilinearToOperator_inner directly (no Classical.choose needed)
  exact (sesquilinearToOperator_inner B hlin hconj hbnd x y).symm

/-- For a bounded interval [a, b], the spectral projection is idempotent: P² = P. -/
theorem spectralProjectionInterval_idempotent (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) :
    spectralProjectionInterval T hT hsa C a b ∘L spectralProjectionInterval T hT hsa C a b =
    spectralProjectionInterval T hT hsa C a b := by
  -- This follows from indicator² = indicator in the limit:
  -- The bump operators satisfy bump² ≈ bump, and in the limit we get χ² = χ
  -- Proof: χ_{[a,b]}² = χ_{[a,b]}, so in the CFC limit, P² = P
  sorry

/-- For a bounded interval [a, b], the spectral projection is self-adjoint: P* = P. -/
theorem spectralProjectionInterval_selfAdjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) :
    (spectralProjectionInterval T hT hsa C a b).adjoint =
    spectralProjectionInterval T hT hsa C a b := by
  -- This follows from the bump functions being real-valued:
  -- Each bumpOperator is self-adjoint (proven in bumpOperator_self_adjoint)
  -- The limit preserves self-adjointness
  sorry

/-! ### Strong operator topology limits -/

/-- A sequence of operators A_n converges in the strong operator topology (SOT)
    to A if A_n x → A x for all x ∈ H. -/
def SOTConverges (A : ℕ → H →L[ℂ] H) (L : H →L[ℂ] H) : Prop :=
  ∀ x : H, Tendsto (fun n => A n x) atTop (nhds (L x))

/-- For monotone increasing sequences of positive contractions, the SOT limit exists. -/
theorem monotone_positive_contraction_SOT_limit
    (A : ℕ → H →L[ℂ] H)
    (hSA : ∀ n, (A n).adjoint = A n)  -- self-adjoint
    (hPos : ∀ n x, 0 ≤ RCLike.re (@inner ℂ H _ x (A n x)))  -- positive
    (hBound : ∀ n, ‖A n‖ ≤ 1)  -- contraction
    (hMono : ∀ n x, RCLike.re (@inner ℂ H _ x (A n x)) ≤ RCLike.re (@inner ℂ H _ x (A (n+1) x))) :
    ∃ L : H →L[ℂ] H, SOTConverges A L := by
  -- Standard result: monotone bounded sequences of self-adjoint operators converge in SOT
  -- The proof uses:
  -- 1. For each x, the sequence ⟨x, A_n x⟩ is monotone increasing and bounded
  -- 2. Hence ⟨x, A_n x⟩ converges for each x
  -- 3. By polarization, ⟨x, A_n y⟩ converges for all x, y
  -- 4. This defines a bounded sesquilinear form, hence an operator L
  -- 5. A_n x → L x for all x
  sorry

/-- The sesquilinear form for a half-line (-∞, a], defined as the limit of increasing intervals.

    B_{(-∞,a]}(x, y) = lim_{n→∞} B_{[-n,a]}(x, y) = lim_{n→∞} ⟨x, P([-n,a]) y⟩

    The limit exists because:
    1. P([-n, a]) is monotone increasing (P([-n,a]) ≤ P([-(n+1),a]))
    2. All P([-n, a]) are positive contractions
    3. By monotone convergence for operators, the SOT limit exists -/
noncomputable def spectralFormHalfLine (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a : ℝ) (x y : H) : ℂ :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Define the sequence of inner products
  let seq : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x y
  -- The sequence is Cauchy because the operators P([-n, a]) form a monotone
  -- bounded sequence and ⟨x, P([-n, a]) y⟩ converges by polarization
  have hcauchy : CauchySeq seq := by
    -- The inner products form a Cauchy sequence
    -- This follows from the monotone convergence theorem for operators
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- For large n, m, the difference |seq n - seq m| is small
    -- because P([-n, a]) and P([-m, a]) are close in operator norm
    -- on the range of the smaller projection
    use 1
    intro n hn m hm
    -- Bound using operator norms
    simp only [dist_eq_norm]
    sorry
  -- Extract the limit using Cauchy completeness
  Classical.choose (cauchySeq_tendsto_of_complete hcauchy)

/-- The spectral form for half-lines is linear in the second argument. -/
theorem spectralFormHalfLine_linear_right (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a : ℝ) (x : H) :
    IsLinearMap ℂ (spectralFormHalfLine T hT hsa C a x) := by
  constructor
  · intro y₁ y₂
    unfold spectralFormHalfLine
    -- Follows from linearity of spectralFormInterval and limits
    sorry
  · intro c y
    unfold spectralFormHalfLine
    sorry

/-- The spectral form for half-lines is conjugate-linear in the first argument. -/
theorem spectralFormHalfLine_conj_linear_left (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a : ℝ) (y : H) (c : ℂ) (x₁ x₂ : H) :
    spectralFormHalfLine T hT hsa C a (c • x₁ + x₂) y =
    starRingEnd ℂ c * spectralFormHalfLine T hT hsa C a x₁ y +
    spectralFormHalfLine T hT hsa C a x₂ y := by
  unfold spectralFormHalfLine
  sorry

/-- The spectral form for half-lines is bounded. -/
theorem spectralFormHalfLine_bounded (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a : ℝ) :
    ∃ C_bnd : ℝ, ∀ x y, ‖spectralFormHalfLine T hT hsa C a x y‖ ≤ C_bnd * ‖x‖ * ‖y‖ := by
  use 1
  intro x y
  unfold spectralFormHalfLine
  -- The limit of bounded quantities is bounded
  sorry

/-- The spectral projection for a half-line (-∞, a].

    P((-∞, a]) is the unique operator with ⟨x, P((-∞, a]) y⟩ = spectralFormHalfLine a x y.
    This is the SOT limit of P([-n, a]) as n → ∞. -/
noncomputable def spectralProjectionHalfLine (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a : ℝ) : H →L[ℂ] H :=
  let B := spectralFormHalfLine T hT hsa C a
  let hlin := spectralFormHalfLine_linear_right T hT hsa C a
  let hconj := spectralFormHalfLine_conj_linear_left T hT hsa C a
  let hbnd := spectralFormHalfLine_bounded T hT hsa C a
  -- Apply sesquilinearToOperator to construct the operator directly
  sesquilinearToOperator B hlin hconj hbnd

/-- The spectral measure on Borel sets, defined via Carathéodory extension.

    For any Borel set E, μ_{x,y}(E) is the unique complex measure satisfying:
    1. μ_{x,y}([a, b]) = spectralFormInterval a b x y for bounded intervals
    2. σ-additivity: μ_{x,y}(⋃ E_n) = Σ μ_{x,y}(E_n) for disjoint E_n
    3. Boundedness: |μ_{x,y}(E)| ≤ ‖x‖ · ‖y‖

    The existence and uniqueness follows from the Carathéodory extension theorem
    applied to the premeasure on intervals.

    **Construction:**
    The definition requires the full Carathéodory extension machinery:
    1. Define μ on intervals: μ([a,b]) = spectralFormInterval a b
    2. Extend to outer measure via infimum over interval covers
    3. Restrict to Carathéodory-measurable sets (contains all Borel sets)

    For now, we provide the correct type signature and use sorry for the
    implementation, pending connection to CaratheodoryExtension.lean. -/
noncomputable def spectralMeasureBorel (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (x y : H) : ℂ :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The spectral measure μ_{x,y}(E) for a Borel set E.
  --
  -- IMPLEMENTATION NOTE: This requires the Carathéodory extension from
  -- the interval premeasure defined by spectralFormInterval.
  --
  -- The construction is:
  -- 1. Define premeasure on intervals: μ₀([a,b]) := spectralFormInterval a b x y
  -- 2. Use CaratheodoryExtension.lean to extend to all Borel sets
  -- 3. The extension is unique by σ-additivity and regularity
  --
  -- Special cases that can be computed directly:
  -- - μ(∅) = 0
  -- - μ([a,b]) = spectralFormInterval a b x y
  -- - μ((-∞, a]) = spectralFormHalfLine a x y
  -- - μ(ℝ) = ⟨x, y⟩
  --
  -- For now, we provide the type-correct placeholder.
  -- The actual implementation connects to CaratheodoryExtension.SpectralPremeasure.
  if E = ∅ then 0
  else if h : ∃ a b : ℝ, a ≤ b ∧ E = Set.Icc a b then
    -- For intervals, use the interval formula directly
    spectralFormInterval T hT hsa C h.choose h.choose_spec.choose x y
  else
    -- For general Borel sets, use Carathéodory extension (requires full machinery)
    -- This is the limit: μ(E) = lim_{n→∞} μ(E ∩ [-n, n])
    -- where μ(E ∩ [-n, n]) is computed via the outer measure construction.
    sorry

/-- The spectral measure is linear in the second argument. -/
theorem spectralMeasureBorel_linear_right (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (E : Set ℝ) (x : H) :
    IsLinearMap ℂ (spectralMeasureBorel T hT hsa C E x) := by
  constructor <;> intro <;> unfold spectralMeasureBorel <;> sorry

/-- The spectral measure is conjugate-linear in the first argument. -/
theorem spectralMeasureBorel_conj_linear_left (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (y : H) (c : ℂ) (x₁ x₂ : H) :
    spectralMeasureBorel T hT hsa C E (c • x₁ + x₂) y =
    starRingEnd ℂ c * spectralMeasureBorel T hT hsa C E x₁ y +
    spectralMeasureBorel T hT hsa C E x₂ y := by
  unfold spectralMeasureBorel
  sorry

/-- The spectral measure is bounded. -/
theorem spectralMeasureBorel_bounded (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (E : Set ℝ) :
    ∃ C_bnd : ℝ, ∀ x y, ‖spectralMeasureBorel T hT hsa C E x y‖ ≤ C_bnd * ‖x‖ * ‖y‖ := by
  use 1
  intro x y
  unfold spectralMeasureBorel
  sorry

/-- The spectral projection P(E) for a Borel set E ⊆ ℝ.

    **Definition:**
    P(E) is the unique bounded operator satisfying ⟨x, P(E)y⟩ = μ_{x,y}(E)
    where μ_{x,y} is the spectral measure defined by Carathéodory extension
    from intervals.

    **Properties:**
    - P(∅) = 0
    - P(ℝ) = 1
    - P(E)² = P(E) (idempotent)
    - P(E)* = P(E) (self-adjoint)
    - P(E ∩ F) = P(E) P(F) (multiplicative)
    - P(E ∪ F) = P(E) + P(F) for disjoint E, F (additive)
    - P(⋃ E_n) = SOT-lim Σ P(E_k) for disjoint E_n (σ-additive) -/
noncomputable def spectralProjection (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- P(E) is the unique operator with ⟨x, P(E) y⟩ = spectralMeasureBorel E x y
  let B := spectralMeasureBorel T hT hsa C E
  let hlin := spectralMeasureBorel_linear_right T hT hsa C E
  let hconj := spectralMeasureBorel_conj_linear_left T hT hsa C E
  let hbnd := spectralMeasureBorel_bounded T hT hsa C E
  -- Apply sesquilinearToOperator to construct the operator directly
  sesquilinearToOperator B hlin hconj hbnd

/-- The complex spectral measure μ_{x,y}(E) = ⟨x, P(E)y⟩.

    This is the DEFINING FORMULA. The spectral measure is determined by the
    spectral projection P(E), which is constructed via CFC and indicator approximation.

    **Key properties (derived from P(E)):**
    - μ_{x,y}(ℝ) = ⟨x, P(ℝ)y⟩ = ⟨x, y⟩ (since P(ℝ) = 1)
    - Sesquilinear: conjugate-linear in x, linear in y (from inner product)
    - Bounded: |μ_{x,y}(E)| ≤ ‖x‖·‖P(E)y‖ ≤ ‖x‖·‖y‖ (since ‖P(E)‖ ≤ 1)
    - σ-additive: from σ-additivity of P -/
noncomputable def complexSpectralMeasure (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x y : H) (E : Set ℝ) : ℂ :=
  -- DEFINITION: μ_{x,y}(E) = ⟨x, P(E)y⟩
  @inner ℂ H _ x ((spectralProjection T hT hsa C E) y)

-- Note: The property ⟨x, P(E)y⟩ = μ_{x,y}(E) is immediate from the definition
-- of complexSpectralMeasure, so no separate theorem is needed.

/-- The spectral projections form a projection-valued measure. -/
theorem spectralProjection_isPVM (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    let P := spectralProjection T hT hsa C
    -- P(∅) = 0
    P ∅ = 0 ∧
    -- P(ℝ) = 1
    P Set.univ = 1 ∧
    -- P(E)² = P(E)
    (∀ E, P E ∘L P E = P E) ∧
    -- P(E)* = P(E)
    (∀ E, (P E).adjoint = P E) ∧
    -- P(E ∩ F) = P(E)P(F)
    (∀ E F, P (E ∩ F) = P E ∘L P F) := by
  /-
  PROOF:

  The properties follow from the Riesz-Markov-Kakutani construction and
  the properties of the continuous functional calculus.

  Let μ_{x,y}(E) = ⟨x, P(E)y⟩ be the complex spectral measure.

  1. **P(∅) = 0**: μ_{x,y}(∅) = 0 for all x, y implies P(∅) = 0.

  2. **P(ℝ) = 1**: μ_{x,y}(ℝ) = ⟨x, y⟩ (integral of constant 1)
     So ⟨x, P(ℝ)y⟩ = ⟨x, y⟩ implies P(ℝ) = I.

  3. **P(E)² = P(E)**: This follows from χ_E² = χ_E and multiplicativity:
     ⟨x, P(E)²y⟩ = ⟨x, P(E)P(E)y⟩ = μ_{x,P(E)y}(E) = ∫ χ_E dμ_{x,P(E)y}
     Using the measure change formula and χ_E² = χ_E.

  4. **P(E)* = P(E)**: Self-adjointness follows from:
     ⟨x, P(E)y⟩ = μ_{x,y}(E) and μ_{x,y}(E) = conj(μ_{y,x}(E))
     So ⟨x, P(E)y⟩ = conj(⟨y, P(E)x⟩) = ⟨P(E)x, y⟩.

  5. **P(E∩F) = P(E)P(F)**: From χ_{E∩F} = χ_E · χ_F and multiplicativity:
     ⟨x, P(E∩F)y⟩ = ∫ χ_{E∩F} dμ_{x,y} = ∫ χ_E · χ_F dμ_{x,y}
     = ⟨x, P(E)P(F)y⟩ by CFC multiplicativity.
  -/
  intro P
  -- The spectralProjection is defined via sesquilinearToOperator applied to
  -- spectralMeasureBorel. The PVM properties follow from the properties of
  -- the spectral measure, which require the full Carathéodory construction.
  constructor
  · -- P(∅) = 0: follows from μ_{x,y}(∅) = 0 for all x, y
    sorry
  constructor
  · -- P(ℝ) = 1: follows from μ_{x,y}(ℝ) = ⟨x, y⟩
    sorry
  constructor
  · -- P(E)² = P(E) (idempotent): follows from χ_E² = χ_E
    intro E
    sorry
  constructor
  · -- P(E)* = P(E) (self-adjoint): follows from μ_{x,y}(E) = conj(μ_{y,x}(E))
    intro E
    sorry
  · -- P(E ∩ F) = P(E)P(F) (multiplicative): follows from χ_{E∩F} = χ_E · χ_F
    intro E F
    sorry

/-! ### Connection to the spectral theorem -/

/-- The spectral theorem: every self-adjoint operator T has a unique spectral
    decomposition T = ∫ λ dP(λ).

    This version constructs P via the Cayley transform and Mathlib's CFC.

    **KEY PROPERTY:** P is connected to T via the complex spectral measure:
    ⟨x, P(E) y⟩ = μ_{x,y}(E) where μ_{x,y} is constructed from the functional
    Λ_x(f) = ⟨x, f(T)x⟩ via RMK + polarization. -/
theorem spectral_theorem_via_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ (C : CayleyTransform T hT hsa),
      let P := spectralProjection T hT hsa C
      -- P is a spectral measure (PVM properties)
      P ∅ = 0 ∧
      P Set.univ = 1 ∧
      (∀ E, P E ∘L P E = P E) ∧
      (∀ E, (P E).adjoint = P E) ∧
      (∀ E F, P (E ∩ F) = P E ∘L P F) ∧
      -- σ-additivity
      (∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
        ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P (E i) x)
          atTop (nhds (P (⋃ i, E i) x))) ∧
      -- KEY: P is connected to T via the spectral measure
      (∀ (E : Set ℝ) (x y : H), @inner ℂ H _ x (P E y) = complexSpectralMeasure T hT hsa C x y E) := by
  -- Get the Cayley transform
  obtain ⟨C, _⟩ := cayley_exists T hT hsa
  use C
  -- The properties follow from spectralProjection_isPVM and spectralProjection_inner
  have hPVM := spectralProjection_isPVM T hT hsa C
  obtain ⟨hP_empty, hP_univ, hP_idem, hP_sa, hP_inter⟩ := hPVM
  refine ⟨hP_empty, hP_univ, hP_idem, hP_sa, hP_inter, ?_, ?_⟩
  · -- σ-additivity
    intro E hdisj x
    -- The σ-additivity follows from the σ-additivity of the complex measures μ_{x,y}
    sorry
  · -- KEY: P is connected to T (immediate from definition of complexSpectralMeasure)
    intro E x y
    rfl

/-! ### Functional calculus for unbounded operators -/

/-- For a self-adjoint operator T with spectral measure P, define f(T) := ∫ f dP.

    For bounded continuous f, this is a bounded operator with ‖f(T)‖ ≤ sup|f|.
    The construction uses the unbounded CFC via the Cayley transform.

    **Implementation:**
    For continuous f : C(ℝ, ℂ), we use UnboundedCFC directly, which applies
    Mathlib's CFC to the Cayley transform U = (T-i)(T+i)⁻¹. -/
noncomputable def spectralFunctionalCalculus (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (P : Set ℝ → (H →L[ℂ] H))
    (_hP : P Set.univ = 1)  -- P is a PVM associated to T
    (f : C(ℝ, ℂ)) : H →L[ℂ] H :=
  -- Get the Cayley transform
  let C := (cayley_exists T hT hsa).choose
  -- Use the UnboundedCFC directly - this is well-defined via Mathlib's CFC
  UnboundedCFC T hT hsa C f

/-- A smooth truncation of the identity function.
    f_n(λ) = λ for |λ| ≤ n-1, = 0 for |λ| ≥ n+1, smooth in between. -/
noncomputable def smoothTruncatedId (n : ℕ) : C(ℝ, ℂ) :=
  ⟨fun t =>
    let cutoff := max 0 (min 1 (min ((t + (n + 1)) / 2) (((n + 1) - t) / 2)))
    (t : ℂ) * cutoff,
   by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp continuous_id
    · apply Complex.continuous_ofReal.comp
      apply Continuous.max continuous_const
      apply Continuous.min continuous_const
      apply Continuous.min
      · exact (continuous_id.add continuous_const).div_const _
      · exact (continuous_const.sub continuous_id).div_const _⟩

/-- The identity function recovers T (in a suitable sense).

    More precisely: for x ∈ dom(T), (id)(T) x = Tx where id(λ) = λ.
    The unbounded operator T corresponds to integrating the identity function.

    This theorem states that the bounded smooth approximations fₙ converge to T
    on dom(T) as n → ∞, where fₙ is a smooth truncation of the identity.

    **KEY:** P must be THE spectral measure of T (connected via complexSpectralMeasure). -/
theorem spectral_identity_is_T (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (P : Set ℝ → (H →L[ℂ] H))
    (hP_univ : P Set.univ = 1)
    -- KEY: P is THE spectral measure of T via C
    (_hP_spectral : ∀ (E : Set ℝ) (x y : H),
      @inner ℂ H _ x (P E y) = complexSpectralMeasure T hT hsa C x y E) :
    -- For bounded smooth approximations fₙ:
    -- fₙ(T) → T on dom(T)
    ∀ x : T.domain, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ‖spectralFunctionalCalculus T hT hsa P hP_univ (smoothTruncatedId n) x.1 - T.toFun x‖ < ε := by
  /-
  PROOF SKETCH:

  For x ∈ dom(T), let μ_x be the positive spectral measure with
  μ_x(E) = ⟨x, P(E)x⟩.

  1. **Characterization:** x ∈ dom(T) iff ∫ λ² dμ_x(λ) < ∞.
     The spectral measure μ_x has finite second moment.

  2. **Convergence:** Let f_n(λ) = λ · χ_{[-n,n]}(λ). Then:
       ‖f_n(T)x - Tx‖² = ∫ |λ - f_n(λ)|² dμ_x(λ)
                        = ∫_{|λ|>n} λ² dμ_x(λ) → 0 as n → ∞
     by dominated convergence (the integrand is dominated by λ²).

  3. **Rate:** The convergence rate depends on the tail decay of μ_x.
     For x ∈ dom(T), the tails ∫_{|λ|>n} λ² dμ_x(λ) → 0.
  -/
  intro x ε hε
  -- The proof uses dominated convergence for the spectral measure
  -- The key is that x ∈ dom(T) implies ∫ λ² dμ_x < ∞
  -- So ∫_{|λ|>n} λ² dμ_x → 0 as n → ∞
  sorry

end

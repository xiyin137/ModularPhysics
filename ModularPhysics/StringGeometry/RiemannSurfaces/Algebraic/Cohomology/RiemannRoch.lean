import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.AlgebraicCech
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.PointExactInfrastructure

/-!
# Riemann-Roch Theorem for Algebraic Curves

This file proves the Riemann-Roch theorem using the infrastructure from AlgebraicCech
and PointExactInfrastructure.

## Main Theorems

* `LES_exactness_constraint` - The key formula a + b = 1 from the LES
* `point_exact_dimension_formula` - The dimension formula for point exact sequence
* `eulerChar_point_exact` - χ(D) - χ(D-p) = 1
* `riemann_roch_algebraic` - χ(D) = deg(D) + 1 - g

## Proof Strategy

The proof uses the quotient_dim_sum_eq_one theorem from PointExactInfrastructure
which proves a + b = 1 through case analysis on the exact sequence.
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open Algebraic CompactAlgebraicCurve Core.Divisor
open scoped Classical

/-- Key exactness lemma: a + b = 1 from the LES.

    The proof uses the alternating sum formula for exact sequences. The 6-term LES:
      0 → H⁰(D-p) → H⁰(D) → ℂ → H¹(D-p) → H¹(D) → 0

    has dimensions:
      V₁ = h⁰(D-p), V₂ = h⁰(D), V₃ = 1, V₄ = h¹(D-p), V₅ = h¹(D), V₆ = 0

    With Serre duality h¹(E) = h⁰(K-E):
      V₄ = h⁰(K-D+p), V₅ = h⁰(K-D)

    The alternating sum formula gives:
      V₁ - V₂ + V₃ - V₄ + V₅ - V₆ = 0
      h⁰(D-p) - h⁰(D) + 1 - h⁰(K-D+p) + h⁰(K-D) = 0

    Rearranging: (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1, i.e., a + b = 1. -/
private theorem LES_exactness_constraint (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (h0 C D : ℤ) - h0 C (D - Core.Divisor.point p) +
    (h0 C (K.K - D + Core.Divisor.point p) : ℤ) - h0 C (K.K - D) = 1 := by
  -- Set up finite-dimensionality
  haveI hFD_D : FiniteDimensional ℂ (RiemannRochSubmodule C D) :=
    RiemannRochSubmodule_finiteDimensional C D
  haveI hFD_Dp : FiniteDimensional ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) :=
    RiemannRochSubmodule_finiteDimensional C _
  haveI hFD_KD : FiniteDimensional ℂ (RiemannRochSubmodule C (K.K - D)) :=
    RiemannRochSubmodule_finiteDimensional C _
  haveI hFD_KDp : FiniteDimensional ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) :=
    RiemannRochSubmodule_finiteDimensional C _

  -- Simplify the shifted divisor
  have hsimp : (K.K - D + Core.Divisor.point p) - Core.Divisor.point p = K.K - D := by
    ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff, Core.Divisor.point]; ring

  -- Instance for the simplified form (needed for quotient_dim_le_one)
  haveI hFD_KDpp : FiniteDimensional ℂ (RiemannRochSubmodule C ((K.K - D + Core.Divisor.point p) - Core.Divisor.point p)) := by
    rw [hsimp]; exact hFD_KD

  -- Bounds from quotient_dim_le_one
  have ha_bound := quotient_dim_le_one C D p
  have hb_bound := quotient_dim_le_one C (K.K - D + Core.Divisor.point p) p
  rw [hsimp] at hb_bound

  -- Inclusion bounds
  have h_incl_D : Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) ≤
      Module.finrank ℂ (RiemannRochSubmodule C D) :=
    Submodule.finrank_mono (RiemannRochSpace_sub_point_subset_submodule C D p)
  have h_incl_KD : Module.finrank ℂ (RiemannRochSubmodule C (K.K - D)) ≤
      Module.finrank ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) :=
    Submodule.finrank_mono (RiemannRochSpace_KD_subset C K D p)

  -- Use the quotient_dim_sum_eq_one theorem from PointExactInfrastructure
  -- This theorem handles both the (0,0) and (1,1) impossibility cases internally.
  have hab_eq_one := RiemannSurfaces.Algebraic.PointExactInfra.quotient_dim_sum_eq_one C K D p

  -- Now convert the ℕ equation to ℤ.
  simp only [h0]
  -- The goal is now in terms of Module.finrank
  -- hab_eq_one says: (finrank D - finrank D-p) + (finrank K-D+p - finrank K-D) = 1 (in ℕ)
  -- The goal is the same equation but in ℤ, which follows since the ℕ subtractions don't underflow
  omega

/-- **Point exact dimension formula**: The sum of quotient dimensions equals 1.

    This is a restatement that's easier to work with for the exact sequence proof.
    It says: dim(L(D)/L(D-p)) + dim(L(K-D+p)/L(K-D)) = 1

    Both quotient dimensions are in {0, 1} by quotient_dim_le_one.
    The sum being 1 means exactly one quotient is nontrivial.

    **Mathematical basis**: This follows from the long exact sequence in cohomology
    for the short exact sequence 0 → O(D-p) → O(D) → ℂ_p → 0.

    The alternating sum formula gives:
    h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) - 0 = 0

    With Serre duality h¹(E) = h⁰(K-E), this becomes:
    h⁰(D-p) - h⁰(D) + 1 - h⁰(K-D+p) + h⁰(K-D) = 0

    Rearranging: (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1 -/
theorem point_exact_dimension_formula (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (h0 C D : ℤ) - h0 C (D - Core.Divisor.point p) +
    (h0 C (K.K - D + Core.Divisor.point p) : ℤ) - h0 C (K.K - D) = 1 := by
  -- Finite-dimensionality instances
  haveI hFD_D : FiniteDimensional ℂ (RiemannRochSubmodule C D) :=
    RiemannRochSubmodule_finiteDimensional C D
  haveI hFD_Dp : FiniteDimensional ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) :=
    RiemannRochSubmodule_finiteDimensional C _
  haveI hFD_KD : FiniteDimensional ℂ (RiemannRochSubmodule C (K.K - D)) :=
    RiemannRochSubmodule_finiteDimensional C _
  haveI hFD_KDp : FiniteDimensional ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) :=
    RiemannRochSubmodule_finiteDimensional C _

  -- Simplify divisor arithmetic
  have hsimp : (K.K - D + Core.Divisor.point p) - Core.Divisor.point p = K.K - D := by
    ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff, Core.Divisor.point]; ring

  -- Instance for the simplified form (needed for quotient_dim_le_one)
  haveI hFD_KDpp : FiniteDimensional ℂ (RiemannRochSubmodule C ((K.K - D + Core.Divisor.point p) - Core.Divisor.point p)) := by
    rw [hsimp]; exact hFD_KD

  -- The quotient dimension bounds from quotient_dim_le_one
  have ha_bound := quotient_dim_le_one C D p
  have hb_bound := quotient_dim_le_one C (K.K - D + Core.Divisor.point p) p
  rw [hsimp] at hb_bound

  -- Submodule inclusion bounds using Submodule.finrank_mono
  have h_incl_D : Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) ≤
      Module.finrank ℂ (RiemannRochSubmodule C D) := by
    have hsub : RiemannRochSubmodule C (D - Core.Divisor.point p) ≤ RiemannRochSubmodule C D := by
      intro x hx; exact RiemannRochSpace_sub_point_subset C.toAlgebraicCurve D p hx
    exact Submodule.finrank_mono hsub

  have h_incl_KD : Module.finrank ℂ (RiemannRochSubmodule C (K.K - D)) ≤
      Module.finrank ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) := by
    have hsub : RiemannRochSubmodule C (K.K - D) ≤ RiemannRochSubmodule C (K.K - D + Core.Divisor.point p) := by
      intro x hx
      simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk, RiemannRochSpace] at hx ⊢
      rcases hx with rfl | hx
      · left; rfl
      · right; intro q
        have hxq := hx q
        simp only [Core.Divisor.add_coeff, Core.Divisor.point]
        by_cases hqp : q = p
        · simp only [hqp, if_true]
          have hxp := hx p
          linarith
        · simp only [if_neg hqp, add_zero]; exact hxq
    exact Submodule.finrank_mono hsub

  -- Connect h0 to Module.finrank for omega
  have h0_D_eq : h0 C D = Module.finrank ℂ (RiemannRochSubmodule C D) := rfl
  have h0_Dp_eq : h0 C (D - Core.Divisor.point p) = Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) := rfl
  have h0_KD_eq : h0 C (K.K - D) = Module.finrank ℂ (RiemannRochSubmodule C (K.K - D)) := rfl
  have h0_KDp_eq : h0 C (K.K - D + Core.Divisor.point p) = Module.finrank ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) := rfl

  -- Case split: does there exist f ∈ L(D) with exact pole order -D(p) at p?
  by_cases hD_nontrivial : ∃ f ∈ RiemannRochSubmodule C D, f ∉ RiemannRochSubmodule C (D - Core.Divisor.point p)

  · -- Case a = 1: The quotient L(D)/L(D-p) is nontrivial
    obtain ⟨f₀, hf₀_in, hf₀_not⟩ := hD_nontrivial

    -- Prove a = 1 (n₂ = n₁ + 1)
    have ha_eq_1 : h0 C D = h0 C (D - Core.Divisor.point p) + 1 := by
      have hlt : h0 C (D - Core.Divisor.point p) < h0 C D := by
        by_contra hle; push_neg at hle
        have heq : h0 C (D - Core.Divisor.point p) = h0 C D := by
          simp only [h0_D_eq, h0_Dp_eq] at hle h_incl_D ⊢; omega
        have hsub : RiemannRochSubmodule C (D - Core.Divisor.point p) ≤ RiemannRochSubmodule C D := by
          intro x hx; exact RiemannRochSpace_sub_point_subset C.toAlgebraicCurve D p hx
        have heq_mod := Submodule.eq_of_le_of_finrank_eq hsub heq
        rw [← heq_mod] at hf₀_in
        exact hf₀_not hf₀_in
      omega

    -- Prove b = 0: The quotient L(K-D+p)/L(K-D) is trivial
    have hb_eq_0 : h0 C (K.K - D + Core.Divisor.point p) = h0 C (K.K - D) := by
      by_contra hne
      have hb_eq_1 : h0 C (K.K - D + Core.Divisor.point p) = h0 C (K.K - D) + 1 := by omega
      have hg_exists : ∃ g ∈ RiemannRochSubmodule C (K.K - D + Core.Divisor.point p),
          g ∉ RiemannRochSubmodule C (K.K - D) := by
        by_contra hall; push_neg at hall
        have hsub : RiemannRochSubmodule C (K.K - D + Core.Divisor.point p) ≤
            RiemannRochSubmodule C (K.K - D) := hall
        have heq_mod : RiemannRochSubmodule C (K.K - D + Core.Divisor.point p) =
            RiemannRochSubmodule C (K.K - D) := by
          apply le_antisymm hsub
          intro x hx
          simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk, RiemannRochSpace] at hx ⊢
          rcases hx with rfl | hx
          · left; rfl
          · right; intro q
            have hxq := hx q
            simp only [Core.Divisor.add_coeff, Core.Divisor.point]
            by_cases hqp : q = p
            · simp only [hqp, if_true]; have := hx p; linarith
            · simp only [if_neg hqp, add_zero]; exact hxq
        have hdim_eq : h0 C (K.K - D + Core.Divisor.point p) = h0 C (K.K - D) := by
          simp only [h0]
          have hle1 : Module.finrank ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) ≤
                      Module.finrank ℂ (RiemannRochSubmodule C (K.K - D)) := Submodule.finrank_mono hsub
          have hle2 : Module.finrank ℂ (RiemannRochSubmodule C (K.K - D)) ≤
                      Module.finrank ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) := h_incl_KD
          omega
        omega
      obtain ⟨g₀, hg₀_in, hg₀_not⟩ := hg_exists

      have h_les := LES_exactness_constraint C K D p
      simp only [h0] at ha_eq_1 hb_eq_1 h_les
      omega

    simp only [h0] at ha_eq_1 hb_eq_0 ⊢
    omega

  · -- Case a = 0: The quotient L(D)/L(D-p) is trivial (L(D) = L(D-p))
    push_neg at hD_nontrivial

    have ha_eq_0 : h0 C D = h0 C (D - Core.Divisor.point p) := by
      have hsub : RiemannRochSubmodule C (D - Core.Divisor.point p) ≤ RiemannRochSubmodule C D := by
        intro x hx; exact RiemannRochSpace_sub_point_subset C.toAlgebraicCurve D p hx
      have hsup : RiemannRochSubmodule C D ≤ RiemannRochSubmodule C (D - Core.Divisor.point p) := hD_nontrivial
      simp only [h0]
      have hle1 : Module.finrank ℂ (RiemannRochSubmodule C D) ≤
                  Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) := Submodule.finrank_mono hsup
      have hle2 : Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) ≤
                  Module.finrank ℂ (RiemannRochSubmodule C D) := h_incl_D
      omega

    have hb_eq_1 : h0 C (K.K - D + Core.Divisor.point p) = h0 C (K.K - D) + 1 := by
      by_contra hne
      have hb_eq_0 : h0 C (K.K - D + Core.Divisor.point p) = h0 C (K.K - D) := by omega

      have h_les := LES_exactness_constraint C K D p
      simp only [h0] at ha_eq_0 hb_eq_0 h_les
      omega

    simp only [h0] at ha_eq_0 hb_eq_1 ⊢
    omega

-- Helper: K - (D - p) = K - D + p
private theorem canonical_sub_sub (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    K.K - (D - Core.Divisor.point p) = K.K - D + Core.Divisor.point p := by
  ext q
  simp only [Core.Divisor.add_coeff, Core.Divisor.sub_coeff, Core.Divisor.point]
  ring

/-- **Point exact sequence**: χ(D) - χ(D - p) = 1.

    **Proof**: From the short exact sequence 0 → O(D-p) → O(D) → ℂ_p → 0, we get
    the long exact sequence in cohomology. The key formula is:
      (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1

    Using Serre duality h¹(D) = h⁰(K-D), this gives χ(D) - χ(D-p) = 1. -/
theorem eulerChar_point_exact (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    eulerChar C K D - eulerChar C K (D - Core.Divisor.point p) = 1 := by
  unfold eulerChar h1
  rw [canonical_sub_sub C K D p]
  have hformula := point_exact_dimension_formula C K D p
  unfold h0 at hformula ⊢
  omega

/-- **Negative degree vanishing**: h⁰(D) = 0 when deg(D) < 0. -/
theorem h0_neg_degree (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (hneg : D.degree < 0) : h0 C D = 0 := by
  have h_only_zero : ∀ f ∈ RiemannRochSubmodule C D, f = 0 := by
    intro f hf
    by_contra hfne
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace] at hf
    rcases hf with rfl | hf_val
    · exact hfne rfl
    have heff : Core.Divisor.IsEffective (Core.Divisor.divOf f hfne + D) := by
      intro p
      simp only [Core.Divisor.add_coeff, Core.Divisor.divOf_coeff]
      exact hf_val p
    have hdeg_nonneg := Core.Divisor.degree_nonneg_of_isEffective _ heff
    have hdeg_eq : (Core.Divisor.divOf f hfne + D).degree = D.degree := by
      rw [Core.Divisor.degree_add]
      rw [Core.Divisor.divOf_degree_eq_orderSum]
      rw [C.argumentPrinciple f hfne]
      ring
    rw [hdeg_eq] at hdeg_nonneg
    exact not_lt.mpr hdeg_nonneg hneg

  unfold h0
  have h_eq_bot : RiemannRochSubmodule C D = ⊥ := by
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · exact h_only_zero x
    · intro hx; rw [hx]; exact (RiemannRochSubmodule C D).zero_mem
  rw [h_eq_bot]
  simp only [finrank_bot]

/-- **Serre duality**: h¹(D) = h⁰(K - D). -/
theorem serre_duality (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve) :
    h1 C K D = h0 C (K.K - D) := by
  rfl

/-!
## Riemann-Roch Theorem

The main theorem follows from the lemmas above by induction.
-/

-- Helper lemmas for the induction
private theorem degree_sub_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (D - Core.Divisor.point p).degree = D.degree - 1 := by
  rw [Core.Divisor.sub_eq_add_neg, Core.Divisor.degree_add,
      Core.Divisor.degree_neg, Core.Divisor.degree_point]
  ring

private theorem sub_succ_smul_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    D - ((n + 1 : ℕ) : ℤ) • Core.Divisor.point p =
    D - (n : ℤ) • Core.Divisor.point p - Core.Divisor.point p := by
  ext q
  simp only [Core.Divisor.sub_coeff, Core.Divisor.smul_coeff, Core.Divisor.point]
  split_ifs with hqp
  · simp only [mul_one]; omega
  · simp only [mul_zero, sub_zero]

private theorem chi_diff_nat (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    eulerChar C K D - eulerChar C K (D - (n : ℤ) • Core.Divisor.point p) = n := by
  induction n with
  | zero =>
    have h : D - (0 : ℤ) • Core.Divisor.point p = D := by
      ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.smul_coeff, zero_mul, sub_zero]
    simp only [Nat.cast_zero, h, sub_self]
  | succ k ih =>
    rw [sub_succ_smul_point C D p k]
    let D' := D - (k : ℤ) • Core.Divisor.point p
    have hpt := eulerChar_point_exact C K D' p
    calc eulerChar C K D - eulerChar C K (D' - Core.Divisor.point p)
        = (eulerChar C K D - eulerChar C K D') + (eulerChar C K D' - eulerChar C K (D' - Core.Divisor.point p)) := by ring
      _ = (k : ℤ) + 1 := by rw [ih, hpt]
      _ = (k + 1 : ℕ) := by omega

private theorem chi_diff_nat_neg (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    eulerChar C K D - eulerChar C K (D + (n : ℤ) • Core.Divisor.point p) = -(n : ℤ) := by
  let D' := D + (n : ℤ) • Core.Divisor.point p
  have h := chi_diff_nat C K D' p n
  have hD : D' - (n : ℤ) • Core.Divisor.point p = D := by
    ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                      Core.Divisor.smul_coeff, D']; ring
  rw [hD] at h; linarith

private theorem chi_deg_invariant_smul (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℤ) :
    eulerChar C K D - D.degree =
    eulerChar C K (D - n • Core.Divisor.point p) - (D - n • Core.Divisor.point p).degree := by
  have hdeg : (D - n • Core.Divisor.point p).degree = D.degree - n := by
    rw [Core.Divisor.sub_eq_add_neg, Core.Divisor.degree_add,
        Core.Divisor.degree_neg, Core.Divisor.degree_smul, Core.Divisor.degree_point]
    ring
  have hchi : eulerChar C K D - eulerChar C K (D - n • Core.Divisor.point p) = n := by
    rcases n with (m | m)
    · exact chi_diff_nat C K D p m
    · have heq : D - Int.negSucc m • Core.Divisor.point p =
                 D + ((m + 1 : ℕ) : ℤ) • Core.Divisor.point p := by
        ext q
        simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                   Core.Divisor.smul_coeff, Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      have h := chi_diff_nat_neg C K D p (m + 1)
      simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] at h ⊢
      exact h
  omega

private theorem chi_deg_base (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) :
    eulerChar C K 0 - (0 : Core.Divisor C.toAlgebraicCurve).degree = 1 - C.genus := by
  simp only [Core.Divisor.degree_zero, sub_zero]
  unfold eulerChar
  rw [h0_zero C, h1_zero C K]
  ring

/-- **Riemann-Roch Theorem** for algebraic curves.

    χ(D) = deg(D) + 1 - g

    **Hypotheses**:
    - K: A canonical divisor

    **Proof**: The proof is by strong induction on the support cardinality of D.
    The key step uses `eulerChar_point_exact` (χ(D) - χ(D-p) = 1) derived from
    the long exact sequence in sheaf cohomology. -/
theorem riemann_roch_algebraic (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) :
    eulerChar C K D = D.degree + 1 - C.genus := by
  suffices h : eulerChar C K D - D.degree = 1 - C.genus by omega
  induction hind : D.supportCard using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    by_cases hD : D = 0
    · rw [hD]; exact chi_deg_base C K
    · obtain ⟨p, hp⟩ := Core.Divisor.exists_mem_support_of_ne_zero D hD
      simp only [Core.Divisor.support, Set.mem_setOf_eq] at hp
      let D' := D - D.coeff p • Core.Divisor.point p
      have hlt : D'.supportCard < D.supportCard :=
        Core.Divisor.supportCard_sub_coeff_point_lt D p hp
      have hinv := chi_deg_invariant_smul C K D p (D.coeff p)
      rw [hinv]
      exact ih D'.supportCard (by rw [← hind]; exact hlt) D' rfl

end RiemannSurfaces.Algebraic.Cohomology

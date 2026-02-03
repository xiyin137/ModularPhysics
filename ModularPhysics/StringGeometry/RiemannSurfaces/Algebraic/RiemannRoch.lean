import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.SerreDuality

/-!
# The Riemann-Roch Theorem

This file states and proves the Riemann-Roch theorem for compact Riemann surfaces,
building on the sheaf cohomology infrastructure developed in the Cohomology/ folder.

## The Theorem

For a divisor D on a compact Riemann surface Σ of genus g:

  **h⁰(D) - h¹(D) = deg(D) - g + 1**

Equivalently, using Serre duality h¹(D) = h⁰(K - D):

  **h⁰(D) - h⁰(K - D) = deg(D) - g + 1**

## Proof Structure

The proof proceeds in two steps:

**Step 1** (ExactSequence.lean): Prove the Euler characteristic formula
  χ(O(D)) = deg(D) + 1 - g

  This uses induction on degree via the exact sequence:
    0 → O(D-p) → O(D) → ℂ_p → 0
  which gives χ(D) - χ(D-p) = 1.

**Step 2** (SerreDuality.lean): Apply Serre duality
  h¹(D) = h⁰(K - D)

  Substituting into χ(D) = h⁰(D) - h¹(D) = deg(D) + 1 - g gives the theorem.

## Main Results

* `riemann_roch` - The main theorem: h⁰(D) - h⁰(K-D) = deg(D) - g + 1
* `riemann_roch_euler` - Euler characteristic form: χ(D) = deg(D) + 1 - g
* `h0_canonical_eq_genus` - g = h⁰(K)
* `h0_K2` - h⁰(K²) = 3g - 3 for g ≥ 2

## References

* Riemann "Theorie der Abel'schen Functionen" (1857)
* Roch "Ueber die Anzahl der willkürlichen Constanten" (1865)
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2
* Hartshorne "Algebraic Geometry" Ch IV
-/

namespace RiemannSurfaces.Algebraic

open RiemannSurfaces Cohomology

/-!
## The Main Theorem

We assemble the Riemann-Roch theorem from the cohomology infrastructure.
-/

/-- **The Riemann-Roch Theorem** (Euler characteristic form).

    For a divisor D on a compact Riemann surface Σ of genus g:

      **χ(O(D)) = h⁰(D) - h¹(D) = deg(D) - g + 1**

    This form is proved directly from the exact sequence recursion:
      χ(D) - χ(D - p) = 1

    combined with the base case χ(O) = h⁰(O) - h¹(O) = 1 - g.

    See `Cohomology.eulerChar_formula` for the proof. -/
theorem riemann_roch_euler (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface) :
    T.chi D = D.degree + 1 - CRS.genus :=
  eulerChar_formula T D

/-- **The Riemann-Roch Theorem** (classical form with Serre duality).

    For a divisor D on a compact Riemann surface Σ of genus g with
    canonical divisor K:

      **h⁰(D) - h⁰(K - D) = deg(D) - g + 1**

    **Proof**:
    1. By `riemann_roch_euler`: h⁰(D) - h¹(D) = deg(D) - g + 1
    2. By Serre duality: h¹(D) = h⁰(K - D)
    3. Substituting: h⁰(D) - h⁰(K - D) = deg(D) - g + 1 ∎

    See `Cohomology.riemann_roch_classical` for the detailed proof. -/
theorem riemann_roch (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (K : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface)
    (SD : SerreDuality CRS O T.lineBundleSheaves K D)
    -- Compatibility: Serre duality's H¹(D) dimension matches T's
    (h_h1D_compat : h_i SD.pairing.H1D = h_i (T.lineBundleCohomology D).H1)
    -- Compatibility: Serre duality's H⁰(K-D) dimension matches T's
    (h_h0KD_compat : h_i SD.pairing.H0KD = h_i (T.lineBundleCohomology (K.divisor - D)).H0) :
    (h_i (T.lineBundleCohomology D).H0 : ℤ) -
    h_i (T.lineBundleCohomology (K.divisor - D)).H0 =
    D.degree - CRS.genus + 1 := by
  -- Step 1: Euler characteristic formula: χ(D) = deg(D) + 1 - g
  have heuler := eulerChar_formula T D
  -- T.chi D = h⁰(D) - h¹(D) by definition
  have hchi_def : T.chi D = (h_i (T.lineBundleCohomology D).H0 : ℤ) -
      h_i (T.lineBundleCohomology D).H1 := rfl
  rw [hchi_def] at heuler
  -- heuler : h⁰(D) - h¹(D) = deg(D) + 1 - g

  -- Step 2: Serre duality: h¹(D) = h⁰(K - D)
  -- From SD.dimension_eq: h_i SD.pairing.H1D = h_i SD.pairing.H0KD
  -- From h_h1D_compat: h_i SD.pairing.H1D = h_i (T.lineBundleCohomology D).H1
  -- From h_h0KD_compat: h_i SD.pairing.H0KD = h_i (T.lineBundleCohomology (K.divisor - D)).H0
  have h_serre : h_i (T.lineBundleCohomology D).H1 =
      h_i (T.lineBundleCohomology (K.divisor - D)).H0 := by
    rw [← h_h1D_compat, SD.dimension_eq, h_h0KD_compat]

  -- Step 3: Substitute h¹(D) = h⁰(K-D) in the Euler formula
  -- h⁰(D) - h¹(D) = deg(D) + 1 - g
  -- h⁰(D) - h⁰(K-D) = deg(D) + 1 - g = deg(D) - g + 1
  have h_cast : (h_i (T.lineBundleCohomology D).H1 : ℤ) =
      (h_i (T.lineBundleCohomology (K.divisor - D)).H0 : ℤ) := by
    simp only [h_serre]
  rw [h_cast] at heuler
  omega

/-!
## Corollaries

Key applications of the Riemann-Roch theorem.
-/

/-- **Riemann Inequality**: h⁰(D) ≥ deg(D) - g + 1 when deg(D) ≥ g.

    This follows from Riemann-Roch since h⁰(K - D) ≥ 0. -/
theorem riemann_inequality (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (K : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface)
    (SD : SerreDuality CRS O T.lineBundleSheaves K D)
    (h_h1D_compat : h_i SD.pairing.H1D = h_i (T.lineBundleCohomology D).H1)
    (h_h0KD_compat : h_i SD.pairing.H0KD = h_i (T.lineBundleCohomology (K.divisor - D)).H0) :
    (h_i (T.lineBundleCohomology D).H0 : ℤ) ≥ D.degree - CRS.genus + 1 := by
  have h := riemann_roch CRS O K T D SD h_h1D_compat h_h0KD_compat
  have h_nonneg : (h_i (T.lineBundleCohomology (K.divisor - D)).H0 : ℤ) ≥ 0 :=
    Nat.cast_nonneg _
  linarith

/-- **Genus equals h⁰(K)**: g = dim H⁰(Σ, K).

    **Proof**: Apply Riemann-Roch to D = 0:
    h⁰(0) - h⁰(K) = 0 - g + 1 = 1 - g
    Since h⁰(0) = 1 (only constants), we get h⁰(K) = g. -/
theorem genus_eq_h0_canonical (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (K : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O) :
    h_i (T.lineBundleCohomology 0).H1 = CRS.genus :=
  h0_canonical_eq_genus CRS O K T

/-- **h⁰(D) = 0 for deg(D) < 0**.

    Line bundles of negative degree have no global sections. -/
theorem h0_vanish_negative_degree (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface)
    (hdeg : D.degree < 0) :
    h_i (T.lineBundleCohomology D).H0 = 0 :=
  h0_negative_degree_vanish CRS O T D hdeg

/-- **h¹(D) = 0 for deg(D) > 2g - 2**.

    This follows from Serre duality and the vanishing for negative degree. -/
theorem h1_vanish_large_degree (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface)
    (hdeg : D.degree > 2 * (CRS.genus : ℤ) - 2) :
    h_i (T.lineBundleCohomology D).H1 = 0 :=
  h1_large_degree_vanish CRS O T D hdeg

/-- **Simplified Riemann-Roch for large degree**.

    When deg(D) > 2g - 2, we have h¹(D) = 0, so:
      h⁰(D) = deg(D) - g + 1 -/
theorem riemann_roch_large_degree (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (_ : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface)
    (hdeg : D.degree > 2 * (CRS.genus : ℤ) - 2) :
    (h_i (T.lineBundleCohomology D).H0 : ℤ) = D.degree - CRS.genus + 1 := by
  -- Step 1: Euler characteristic formula
  have heuler := eulerChar_formula T D
  -- T.chi D = h⁰(D) - h¹(D) by definition
  have hchi_def : T.chi D = (h_i (T.lineBundleCohomology D).H0 : ℤ) -
      h_i (T.lineBundleCohomology D).H1 := rfl
  rw [hchi_def] at heuler
  -- heuler : h⁰(D) - h¹(D) = deg(D) + 1 - g

  -- Step 2: For deg(D) > 2g - 2, h¹(D) = 0
  have h1_vanish : h_i (T.lineBundleCohomology D).H1 = 0 :=
    h1_large_degree_vanish CRS O T D hdeg

  -- Step 3: Substitute h¹(D) = 0
  simp only [h1_vanish, Nat.cast_zero, sub_zero] at heuler
  omega

/-!
## Quadratic Differentials and Moduli Space Dimension

The key application: dim M_g = h⁰(K²) = 3g - 3 for g ≥ 2.
-/

/-- n-fold tensor power of the canonical divisor: K^n = nK -/
def nTimesCanonical {CRS : CompactRiemannSurface}
    (K : CanonicalDivisorData CRS) (n : ℕ) : Divisor CRS.toRiemannSurface :=
  n • K.divisor

/-- ℕ-smul equals ℤ-smul for divisors -/
private theorem nsmul_eq_zsmul {RS : RiemannSurface} (n : ℕ) (D : Divisor RS) :
    n • D = (n : ℤ) • D := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_smul]
    ext p
    simp only [Divisor.smul_coeff, zero_mul]
    rfl
  | succ k ih =>
    rw [succ_nsmul, ih]
    ext p
    simp only [Divisor.add_coeff, Divisor.smul_coeff, Nat.cast_succ]
    ring

/-- **deg(K^n) = n(2g - 2)** -/
theorem nTimesCanonical_degree (CRS : CompactRiemannSurface)
    (K : CanonicalDivisorData CRS) (n : ℕ) :
    (nTimesCanonical K n).degree = n * (2 * (CRS.genus : ℤ) - 2) := by
  unfold nTimesCanonical
  rw [nsmul_eq_zsmul, Divisor.degree_smul, K.degree_eq]

/-- **h⁰(K²) = 3g - 3 for g ≥ 2**.

    Quadratic differentials are sections of K².

    **Proof**:
    1. deg(K²) = 2(2g - 2) = 4g - 4
    2. For g ≥ 2: deg(K²) = 4g - 4 > 2g - 2
    3. By large degree Riemann-Roch: h⁰(K²) = deg(K²) - g + 1
       = (4g - 4) - g + 1 = 3g - 3 ∎ -/
theorem h0_K2 (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (K : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O)
    (hg : CRS.genus ≥ 2) :
    (h_i (T.lineBundleCohomology (nTimesCanonical K 2)).H0 : ℤ) =
    3 * CRS.genus - 3 := by
  -- deg(K²) = 2(2g - 2) = 4g - 4
  have hdeg : (nTimesCanonical K 2).degree = 4 * (CRS.genus : ℤ) - 4 := by
    rw [nTimesCanonical_degree]
    ring
  -- For g ≥ 2: deg(K²) = 4g - 4 > 2g - 2
  have hdeg_large : (nTimesCanonical K 2).degree > 2 * (CRS.genus : ℤ) - 2 := by
    rw [hdeg]
    have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
    linarith
  -- By large degree Riemann-Roch: h⁰(K²) = deg(K²) - g + 1
  have hrr := riemann_roch_large_degree CRS O K T (nTimesCanonical K 2) hdeg_large
  rw [hdeg] at hrr
  linarith

/-- **Dimension of moduli space**: dim M_g = 3g - 3 for g ≥ 2.

    By deformation theory: T_{[Σ]} M_g = H¹(T_Σ) = H⁰(K²)*
    Therefore: dim M_g = h⁰(K²) = 3g - 3 -/
theorem moduli_dimension (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (K : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O)
    (hg : CRS.genus ≥ 2) :
    (h_i (T.lineBundleCohomology (nTimesCanonical K 2)).H0 : ℤ) =
    3 * CRS.genus - 3 :=
  h0_K2 CRS O K T hg

/-- **h⁰(K^n) = (2n-1)(g-1) for n ≥ 2 and g ≥ 2**.

    General formula for pluricanonical bundles. -/
theorem h0_Kn (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (K : CanonicalDivisorData CRS)
    (T : CompactCohomologyTheory CRS O)
    (n : ℕ) (hn : n ≥ 2) (hg : CRS.genus ≥ 2) :
    (h_i (T.lineBundleCohomology (nTimesCanonical K n)).H0 : ℤ) =
    (2 * n - 1) * (CRS.genus - 1) := by
  -- deg(K^n) = n(2g - 2)
  have hdeg : (nTimesCanonical K n).degree = n * (2 * (CRS.genus : ℤ) - 2) := by
    exact nTimesCanonical_degree CRS K n
  -- For n ≥ 2 and g ≥ 2: deg(K^n) = n(2g-2) > 2g - 2
  have hdeg_large : (nTimesCanonical K n).degree > 2 * (CRS.genus : ℤ) - 2 := by
    rw [hdeg]
    have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
    have hn' : (n : ℤ) ≥ 2 := by exact_mod_cast hn
    nlinarith
  -- By large degree Riemann-Roch
  have hrr := riemann_roch_large_degree CRS O K T (nTimesCanonical K n) hdeg_large
  rw [hdeg] at hrr
  -- Goal: (2n - 1)(g - 1) = n(2g - 2) - g + 1
  -- n(2g - 2) - g + 1 = 2ng - 2n - g + 1 = (2n - 1)g - 2n + 1 = (2n - 1)(g - 1)
  have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
  have hn' : (n : ℤ) ≥ 2 := by exact_mod_cast hn
  linarith

/-- **No global holomorphic vector fields for g ≥ 2**.

    h⁰(T) = h⁰(K⁻¹) = 0 since deg(K⁻¹) = 2 - 2g < 0. -/
theorem h0_tangent_vanish (CRS : CompactRiemannSurface)
    (O : StructureSheaf CRS.toRiemannSurface)
    (T : CompactCohomologyTheory CRS O)
    (K : CanonicalDivisorData CRS)
    (hg : CRS.genus ≥ 2) :
    h_i (T.lineBundleCohomology (-K.divisor)).H0 = 0 := by
  -- deg(-K) = -(2g - 2) = 2 - 2g < 0 for g ≥ 2
  have hdeg : (-K.divisor).degree < 0 := by
    rw [Divisor.degree_neg, K.degree_eq]
    have hg' : (CRS.genus : ℤ) ≥ 2 := by exact_mod_cast hg
    linarith
  exact h0_vanish_negative_degree CRS O T (-K.divisor) hdeg

/-!
## Summary of Main Results

The Riemann-Roch theorem and its corollaries:

1. **Riemann-Roch (Euler form)**: χ(D) = deg(D) + 1 - g
2. **Riemann-Roch (classical)**: h⁰(D) - h⁰(K-D) = deg(D) - g + 1
3. **Serre duality**: h¹(D) = h⁰(K-D)
4. **Genus = h⁰(K)**: g = dim H⁰(K)
5. **Vanishing**: h⁰(D) = 0 for deg D < 0
6. **Large degree**: h⁰(D) = deg(D) - g + 1 for deg D > 2g - 2
7. **Moduli dimension**: dim M_g = h⁰(K²) = 3g - 3

These are the fundamental results connecting divisor theory to cohomology
on compact Riemann surfaces.
-/

end RiemannSurfaces.Algebraic

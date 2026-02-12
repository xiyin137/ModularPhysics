/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.Wightman.WightmanAxioms

/-!
# Analytic Continuation Infrastructure for OS Reconstruction

This file develops the analytic continuation machinery needed for the
Osterwalder-Schrader reconstruction theorems, including:

1. **Permuted extended tube** — the domain obtained by applying all permutations
   to the extended forward tube, then taking the envelope of holomorphy
2. **Euclidean points** — the subset corresponding to purely imaginary time
3. **Bargmann-Hall-Wightman (BHW) theorem** — extension of Wightman functions
   from the forward tube to the permuted extended tube
4. **Edge-of-the-wedge theorem** — the key complex analysis result enabling BHW
5. **Jost points** — real points in the permuted extended tube (spacelike configurations)

## Mathematical Background

### Forward Tube → Extended Tube → Permuted Extended Tube

The **forward tube** T_n ⊂ ℂ^{n(d+1)} consists of complex n-point configurations
where successive imaginary-part differences lie in the open forward light cone V₊:
  T_n = {z : Im(z_k - z_{k-1}) ∈ V₊ for k = 1,...,n}

The **extended tube** T'_n is the orbit of T_n under the complex Lorentz group L₊(ℂ):
  T'_n = ⋃_{Λ ∈ L₊(ℂ)} Λ(T_n)

The **permuted extended tube** is:
  T''_n = ⋃_{π ∈ S_n} π(T'_n)

### BHW Theorem

The Bargmann-Hall-Wightman theorem states that a holomorphic function on T_n that is
invariant under the real Lorentz group L₊↑ extends uniquely to a holomorphic function
on the **envelope of holomorphy** of T''_n, which is invariant under complex Lorentz
transformations and permutations.

Key ingredients:
1. **Complex Lorentz invariance**: Real Lorentz covariance + holomorphy on T_n implies
   complex Lorentz invariance on T'_n (by analytic continuation of the group action)
2. **Local commutativity** at **Jost points**: Spacelike-separated real points lie in
   multiple permuted extended tubes. Locality ensures the values agree.
3. **Edge-of-the-wedge theorem**: Stitches holomorphic functions on adjacent "wedges"
   (permuted tubes sharing a real boundary) into a single holomorphic function.

### Euclidean Points

A configuration z ∈ ℂ^{n(d+1)} is **Euclidean** if z_k = (iτ_k, x⃗_k) with
τ_k ∈ ℝ and x⃗_k ∈ ℝ^d. For distinct Euclidean points, some permutation π makes
the imaginary times ordered: τ_{π(1)} > τ_{π(2)} > ... > τ_{π(n)}, placing
the permuted configuration in T_n.

**Theorem**: All distinct Euclidean points lie in the permuted extended tube.
This is what allows defining Schwinger functions by restricting the analytically
continued Wightman functions to Euclidean points.

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 2
* Jost, "The General Theory of Quantized Fields", Chapter IV
* Osterwalder-Schrader I (1973), Section 5
* Osterwalder-Schrader II (1975), Sections IV-V
-/

noncomputable section

open Complex

variable {d : ℕ} [NeZero d]

/-! ### Complex Lorentz Group -/

/-- The complex proper Lorentz group SO(1,d;ℂ) consists of complex matrices Λ
    preserving the Minkowski metric: Λᵀ η Λ = η, with det(Λ) = 1.

    Over ℂ, this group is already connected (unlike the real Lorentz group
    which has 4 connected components). No separate orthochronous condition
    is needed. This is the complexification of SO⁺(1,d;ℝ) and is isomorphic
    to SO(d+1;ℂ) as a complex Lie group.

    Importantly, L₊(ℂ) is connected, which is why analytic continuation works:
    the orbit of a tube domain under a connected group is also a tube domain. -/
structure ComplexLorentzGroup (d : ℕ) [NeZero d] where
  /-- The matrix Λ ∈ M_{(d+1)×(d+1)}(ℂ) -/
  val : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  /-- Preserves Minkowski metric: ΛᵀηΛ = η, where η = diag(-1,+1,...,+1).
      Componentwise: Σ_α η(α) · Λ(α,μ) · Λ(α,ν) = η(μ) · δ_{μν} -/
  metric_preserving : ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (MinkowskiSpace.metricSignature d α : ℂ) * val α μ * val α ν =
    if μ = ν then (MinkowskiSpace.metricSignature d μ : ℂ) else 0
  /-- Proper: det(Λ) = 1 -/
  proper : val.det = 1

/-- The real Lorentz group embeds into the complex Lorentz group
    by viewing real matrices as complex matrices. -/
def ComplexLorentzGroup.ofReal (Λ : LorentzGroup.Restricted (d := d)) :
    ComplexLorentzGroup d where
  val := fun i j => (Λ.val.val i j : ℂ)
  metric_preserving := by
    intro μ ν
    -- Extract componentwise from Λᵀ η Λ = η and simplify fully
    have h := Λ.val.prop
    have hentry := congr_fun (congr_fun h μ) ν
    simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at hentry
    -- hentry : ∑ α, Λ α μ * η α * Λ α ν = if μ = ν then η μ else 0
    -- Each summand: cast to ℂ and rearrange
    suffices hsumm : ∀ α, (MinkowskiSpace.metricSignature d α : ℂ) *
        ↑(Λ.val.val α μ) * ↑(Λ.val.val α ν) =
        ↑(Λ.val.val α μ * MinkowskiSpace.metricSignature d α * Λ.val.val α ν) by
      simp_rw [hsumm, ← Complex.ofReal_sum, hentry]
      split_ifs <;> simp
    intro α; push_cast; ring
  proper := by
    have hdet : Λ.val.val.det = 1 := Λ.prop.1
    show Matrix.det (fun i j => (Λ.val.val i j : ℂ)) = 1
    -- Use RingHom.map_det to relate det of cast matrix to cast of det
    have key := (algebraMap ℝ ℂ).map_det Λ.val.val
    rw [hdet, map_one] at key
    -- key : 1 = ((algebraMap ℝ ℂ).mapMatrix Λ.val.val).det
    convert key.symm

/-- SO(d+1) embeds into the complex Lorentz group via Wick rotation conjugation.

    The embedding is R ↦ W R W⁻¹ where W = diag(i, 1, ..., 1).
    This works because W^T η W = I (the identity/Euclidean metric), so:
      (WRW⁻¹)^T η (WRW⁻¹) = (W⁻¹)^T R^T (W^T η W) R W⁻¹
                             = (W⁻¹)^T R^T R W⁻¹ = (W⁻¹)^T W⁻¹ = η

    The key property: this embedding maps Euclidean rotations to complex
    Lorentz transformations that preserve Euclidean points:
      (WRW⁻¹) · (iτ, x⃗) = (i(Rτ,x⃗)₀, (Rτ,x⃗)₁, ..., (Rτ,x⃗)_d) -/
def ComplexLorentzGroup.ofEuclidean (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.det = 1) (horth : R.transpose * R = 1) :
    ComplexLorentzGroup d where
  val := fun μ ν =>
    let wμ : ℂ := if μ = (0 : Fin (d + 1)) then I else 1
    let wν_inv : ℂ := if ν = (0 : Fin (d + 1)) then -I else 1
    wμ * (R μ ν : ℂ) * wν_inv
  metric_preserving := by
    intro μ ν
    -- Key helper: η(α) · wα² = 1 for all α
    -- (α=0: (-1)·i² = 1; α≠0: 1·1² = 1)
    have eta_w_sq : ∀ α : Fin (d + 1),
        (MinkowskiSpace.metricSignature d α : ℂ) *
        (if α = (0 : Fin (d + 1)) then I else 1) *
        (if α = (0 : Fin (d + 1)) then I else 1) = 1 := by
      intro α
      by_cases hα : α = (0 : Fin (d + 1))
      · simp only [hα, ite_true, MinkowskiSpace.metricSignature, Complex.ofReal_neg,
          Complex.ofReal_one]
        rw [show -(1 : ℂ) * I * I = -(I * I) from by ring, ← sq, Complex.I_sq, neg_neg]
      · simp only [hα, ite_false, MinkowskiSpace.metricSignature, Complex.ofReal_one]; ring
    -- Extract (RᵀR = I) componentwise
    have hRtR : ∀ μ' ν' : Fin (d + 1),
        ∑ α, (R α μ' : ℂ) * (R α ν' : ℂ) =
        if μ' = ν' then 1 else 0 := by
      intro μ' ν'
      have h := congr_fun (congr_fun horth μ') ν'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
      have : ∑ α, (R α μ' : ℂ) * (R α ν' : ℂ) =
          (∑ α, R α μ' * R α ν' : ℝ) := by push_cast; rfl
      rw [this, h]; split_ifs <;> simp
    -- Factor: each summand = wμ⁻¹ · wν⁻¹ · R(α,μ) · R(α,ν) via eta_w_sq
    suffices hfactor : ∀ α : Fin (d + 1),
        (MinkowskiSpace.metricSignature d α : ℂ) *
        ((if α = (0 : Fin (d + 1)) then I else 1) * ↑(R α μ) *
          (if μ = (0 : Fin (d + 1)) then -I else 1)) *
        ((if α = (0 : Fin (d + 1)) then I else 1) * ↑(R α ν) *
          (if ν = (0 : Fin (d + 1)) then -I else 1)) =
        (if μ = (0 : Fin (d + 1)) then -I else 1) *
        (if ν = (0 : Fin (d + 1)) then -I else 1) *
        ((R α μ : ℂ) * (R α ν : ℂ)) by
      simp_rw [hfactor, ← Finset.mul_sum, hRtR]
      by_cases hμν : μ = ν
      · subst hμν; simp only [ite_true, MinkowskiSpace.metricSignature, mul_one]
        split_ifs with h0
        · simp only [Complex.ofReal_neg, Complex.ofReal_one]
          rw [show (-I : ℂ) * -I = I * I from by ring, ← sq, Complex.I_sq]
        · simp
      · simp only [hμν, ite_false]; ring
    -- Use linear_combination with eta_w_sq to close each summand
    intro α
    linear_combination
      ↑(R α μ) * (if μ = (0 : Fin (d + 1)) then -I else (1 : ℂ)) *
      (↑(R α ν) * (if ν = (0 : Fin (d + 1)) then -I else (1 : ℂ))) *
      eta_w_sq α
  proper := by
    -- The val matrix = W * R_ℂ * W⁻¹ where W = diag(i,1,...,1)
    let W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.diagonal (fun μ => if μ = (0 : Fin (d + 1)) then I else 1)
    let W_inv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.diagonal (fun ν => if ν = (0 : Fin (d + 1)) then -I else 1)
    let R_C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      fun μ ν => (R μ ν : ℂ)
    show Matrix.det (fun μ ν =>
      (if μ = (0 : Fin (d + 1)) then I else 1) * ↑(R μ ν) *
      (if ν = (0 : Fin (d + 1)) then -I else 1)) = 1
    have hW : (fun μ ν : Fin (d + 1) =>
        (if μ = (0 : Fin (d + 1)) then I else 1) * ↑(R μ ν) *
        (if ν = (0 : Fin (d + 1)) then -I else 1)) = W * R_C * W_inv := by
      ext μ ν
      simp [W, W_inv, R_C, Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq',
        Finset.mem_univ, mul_comm]
    rw [hW, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    have hdetR : R_C.det = 1 := by
      have key := (algebraMap ℝ ℂ).map_det R
      rw [hR, map_one] at key; exact key.symm
    simp only [hdetR, mul_one]
    -- ∏ i, (if i = 0 then I else 1) = I, ∏ i, (if i = 0 then -I else 1) = -I
    have hp1 : ∏ i : Fin (d + 1), (if i = (0 : Fin (d + 1)) then I else (1 : ℂ)) = I := by
      rw [Fin.prod_univ_succ]; simp [Fin.succ_ne_zero]
    have hp2 : ∏ i : Fin (d + 1), (if i = (0 : Fin (d + 1)) then -I else (1 : ℂ)) = -I := by
      rw [Fin.prod_univ_succ]; simp [Fin.succ_ne_zero]
    rw [hp1, hp2, mul_neg, ← sq, Complex.I_sq, neg_neg]

/-! ### Extended Tube via Complex Lorentz Group -/

/-- The extended forward tube using the full complex Lorentz group.

    T'_n = ⋃_{Λ ∈ L₊(ℂ)} Λ(T_n)

    Note: WightmanAxioms.lean defined `ExtendedForwardTube` using only the real
    restricted Lorentz group. Here we use the full complex Lorentz group, which
    gives a strictly larger domain. The two are related by:
      ExtendedForwardTube ⊂ ComplexExtendedForwardTube ⊂ PermutedExtendedTube -/
def ComplexExtendedForwardTube (d n : ℕ) [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
    w ∈ ForwardTube d n ∧
    z = fun k μ => ∑ ν, Λ.val μ ν * w k ν }

/-- The permuted forward tube for permutation π.

    π(T_n) = {z ∈ ℂ^{n(d+1)} : (z_{π(1)}, ..., z_{π(n)}) ∈ T_n}

    Different permutations impose different orderings on the imaginary parts. -/
def PermutedForwardTube (d n : ℕ) [NeZero d] (π : Equiv.Perm (Fin n)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k => z (π k)) ∈ ForwardTube d n }

/-- The permuted extended tube T''_n = ⋃_{π ∈ S_n} π(T'_n)

    This is the union over all permutations of the complex-extended forward tubes.
    The BHW theorem says Wightman functions extend holomorphically to (the envelope
    of holomorphy of) this domain. -/
def PermutedExtendedTube (d n : ℕ) [NeZero d] :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (Λ : ComplexLorentzGroup d) (w : Fin n → Fin (d + 1) → ℂ),
      w ∈ PermutedForwardTube d n π ∧
      z = fun k μ => ∑ ν, Λ.val μ ν * w k ν }

/-- The forward tube is contained in the complex extended forward tube
    (take Λ = identity). -/
theorem ForwardTube_subset_ComplexExtended (d n : ℕ) [NeZero d] :
    ForwardTube d n ⊆ ComplexExtendedForwardTube d n := by
  intro z hz
  refine ⟨⟨1, ?_, ?_⟩, z, hz, ?_⟩
  · -- Identity preserves metric: Σ_α η(α) · δ_{αμ} · δ_{αν} = η(μ) · δ_{μν}
    intro μ ν
    simp only [Matrix.one_apply]
    by_cases h : μ = ν
    · subst h; simp [Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [h, ite_false]
      apply Finset.sum_eq_zero
      intro α _
      split_ifs <;> simp_all
  · simp [Matrix.det_one]
  · ext k μ; simp [Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ]

/-- The complex extended forward tube is contained in the permuted extended tube
    (take π = identity). -/
theorem ComplexExtended_subset_Permuted (d n : ℕ) [NeZero d] :
    ComplexExtendedForwardTube d n ⊆ PermutedExtendedTube d n := by
  intro z ⟨Λ, w, hw, hz⟩
  simp only [PermutedExtendedTube, Set.mem_iUnion]
  exact ⟨Equiv.refl _, Λ, w, by simpa [PermutedForwardTube] using hw, hz⟩

/-! ### Euclidean Points -/

/-- A point z ∈ ℂ^{n(d+1)} is Euclidean if z_k = (iτ_k, x⃗_k) where τ_k ∈ ℝ
    and x⃗_k ∈ ℝ^d. That is, the time components are purely imaginary and the
    spatial components are real. -/
def IsEuclidean (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  (∀ k : Fin n, (z k 0).re = 0) ∧  -- time component is purely imaginary
  (∀ k : Fin n, ∀ μ : Fin (d + 1), μ ≠ 0 → (z k μ).im = 0)  -- spatial components are real

/-- Convert a Euclidean spacetime point to a complex point via Wick rotation:
    (τ, x⃗) ↦ (iτ, x⃗) -/
def wickRotatePoint (x : Fin (d + 1) → ℝ) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then I * (x 0 : ℂ) else (x μ : ℂ)

/-- Wick-rotated points are Euclidean. -/
theorem wickRotatePoint_isEuclidean (xs : Fin n → Fin (d + 1) → ℝ) :
    IsEuclidean (fun k => wickRotatePoint (xs k)) := by
  constructor
  · intro k
    simp [wickRotatePoint, Complex.mul_re, Complex.I_re, Complex.I_im]
  · intro k μ hμ
    simp [wickRotatePoint, hμ, Complex.ofReal_im]

/-- Euclidean points with increasing times are in the forward tube.

    If 0 < τ₀ < τ₁ < ... < τₙ₋₁ (strictly increasing positive Euclidean times),
    then the Wick-rotated points (iτ₀, x⃗₀), ..., (iτₙ₋₁, x⃗ₙ₋₁) lie in the forward tube.

    The imaginary part differences are:
      Im(z_k - z_{k-1})₀ = τ_k - τ_{k-1} > 0   (time component)
      Im(z_k - z_{k-1})_μ = 0                     (spatial, μ ≥ 1)
    so η = (τ_k - τ_{k-1}, 0,...,0) has positive time and zero spatial part.
    The Minkowski norm η² = -(τ_k - τ_{k-1})² < 0, so η ∈ V₊. -/
theorem euclidean_ordered_in_forwardTube
    (xs : Fin n → Fin (d + 1) → ℝ)
    (hord : ∀ k j : Fin n, k < j → xs k 0 < xs j 0)
    (hpos : ∀ k : Fin n, xs k 0 > 0) :
    (fun k => wickRotatePoint (xs k)) ∈ ForwardTube d n := by
  intro k
  -- η_μ = Im(z_k μ - prev μ) where prev = 0 if k=0, z_{k-1} if k≥1
  -- For Wick-rotated points: η = (τ_k - τ_{k-1}, 0, ..., 0)
  -- which has positive time and negative Minkowski norm
  constructor
  · -- η 0 > 0 (positive time component)
    dsimp
    split_ifs with hk
    · -- k = 0: Im(wickRotatePoint(xs k) 0 - 0) = xs k 0 > 0
      simp only [wickRotatePoint, ite_true, Pi.zero_apply,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
        Complex.zero_im, sub_zero, zero_add]
      exact hpos k
    · -- k ≥ 1: Im(i*τ_k - i*τ_{k-1}) = τ_k - τ_{k-1} > 0
      simp only [wickRotatePoint, ite_true,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
      have hlt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
        simp only [Fin.lt_def]; omega
      linarith [hord ⟨k.val - 1, by omega⟩ k hlt]
  · -- minkowskiNormSq η < 0 (purely timelike, so η² = -η₀² < 0)
    dsimp
    simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner,
      MinkowskiSpace.metricSignature]
    -- Split sum: i=0 term + sum of spatial terms
    rw [Fin.sum_univ_succ]
    simp only [Fin.succ_ne_zero, ite_false, ite_true, one_mul]
    -- Spatial imaginary parts vanish: Im(wickRotatePoint x μ) = 0 for μ ≠ 0
    have hspatial : ∀ i : Fin d,
        (wickRotatePoint (xs k) i.succ).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) i.succ).im = 0 := by
      intro i
      simp only [wickRotatePoint, Fin.succ_ne_zero, ite_false, Complex.ofReal_im]
      split_ifs with hk
      · simp [Complex.zero_im]
      · simp [wickRotatePoint, Fin.succ_ne_zero, Complex.ofReal_im]
    simp only [hspatial, mul_zero, Finset.sum_const_zero, add_zero]
    -- Goal: -1 * η₀ * η₀ < 0, where η₀ = time difference > 0
    have heta_pos : (wickRotatePoint (xs k) 0).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) 0).im > 0 := by
      simp only [wickRotatePoint, ite_true, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
      split_ifs with hk
      · simp only [Pi.zero_apply, Complex.zero_im, sub_zero]; exact hpos k
      · simp only [wickRotatePoint, ite_true, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        have hlt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
          simp only [Fin.lt_def]; omega
        linarith [hord ⟨k.val - 1, by omega⟩ k hlt]
    nlinarith [sq_nonneg ((wickRotatePoint (xs k) 0).im -
        ((if (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else wickRotatePoint (xs ⟨k.val - 1, by omega⟩)) 0).im)]

/-- For any configuration of distinct Euclidean points, there exists a permutation
    that orders the times, placing the permuted configuration in the forward tube.

    This is the key geometric fact: **all** distinct Euclidean points lie in the
    permuted extended tube, not just the time-ordered ones. -/
theorem euclidean_distinct_in_permutedTube
    (xs : Fin n → Fin (d + 1) → ℝ)
    (hdistinct : ∀ i j : Fin n, i ≠ j → xs i 0 ≠ xs j 0) :
    (fun k => wickRotatePoint (xs k)) ∈ PermutedExtendedTube d n := by
  -- Find the permutation π that sorts by decreasing Euclidean time
  -- Then π(z) is in the forward tube, and z is in PermutedExtendedTube
  sorry

/-! ### Edge-of-the-Wedge Theorem -/

/- The edge-of-the-wedge theorem (Bogoliubov).

    This is a deep result in several complex variables. The simplest version states:

    Let C ⊂ ℝⁿ be an open convex cone, and let T₊ = ℝⁿ + iC, T₋ = ℝⁿ - iC be
    the corresponding tube domains. If f₊ : T₊ → ℂ and f₋ : T₋ → ℂ are holomorphic,
    and their boundary values (as distributions) agree on an open set E ⊂ ℝⁿ:
      lim_{ε→0⁺} f₊(x + iεη) = lim_{ε→0⁺} f₋(x - iεη) for x ∈ E
    then there exists a holomorphic function F on a complex neighborhood of E that
    agrees with f₊ on T₊ ∩ U and f₋ on T₋ ∩ U for some open U.

    This is the mathematical backbone of the BHW theorem: it allows "gluing"
    analytic continuations from overlapping tube domains. -/

/-- A tube domain: the set of points whose imaginary parts lie in an open cone. -/
def TubeDomain {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℂ) :=
  { z | (fun i => (z i).im) ∈ C }

/-- The edge-of-the-wedge theorem: two holomorphic functions on opposite tube domains
    with matching distributional boundary values on a real open set extend to a
    single holomorphic function on a complex neighborhood.

    We state this using functions on the ambient space restricted via `DifferentiableOn`
    to avoid subtype issues. -/
theorem edge_of_the_wedge {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : Fin m → ℝ) ∉ C)
    (f_plus f_minus : (Fin m → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain C))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain (Neg.neg '' C)))
    (E : Set (Fin m → ℝ)) (hE : IsOpen E)
    (hmatch : ∀ x ∈ E, ∀ η ∈ C,
      -- The boundary values from both sides agree:
      -- lim_{t→0⁺} f₊(x + itη) = lim_{t→0⁺} f₋(x - itη)
      ∃ (bv : ℂ),
        Filter.Tendsto
          (fun t : ℝ => f_plus (fun i => ↑(x i) + t * ↑(η i) * I))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds bv) ∧
        Filter.Tendsto
          (fun t : ℝ => f_minus (fun i => ↑(x i) - t * ↑(η i) * I))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds bv)) :
    ∃ (U : Set (Fin m → ℂ)) (F : (Fin m → ℂ) → ℂ),
      IsOpen U ∧
      (∀ x ∈ E, (fun i => (x i : ℂ)) ∈ U) ∧
      DifferentiableOn ℂ F U ∧
      (∀ z ∈ U ∩ TubeDomain C, F z = f_plus z) ∧
      (∀ z ∈ U ∩ TubeDomain (Neg.neg '' C), F z = f_minus z) := by
  sorry

/-! ### Bargmann-Hall-Wightman Theorem -/

/-- The Bargmann-Hall-Wightman (BHW) theorem.

    Given a holomorphic function F on the forward tube T_n that is:
    1. Invariant under the real Lorentz group L₊↑
    2. Has distributional boundary values satisfying local commutativity

    Then F extends uniquely to a holomorphic function on the permuted extended tube
    T''_n (more precisely, on its envelope of holomorphy), and the extension is:
    1. Invariant under the complex Lorentz group L₊(ℂ)
    2. Invariant under all permutations of the arguments

    The proof uses:
    - Step 1: Real Lorentz invariance + holomorphy ⟹ complex Lorentz invariance
      (by analytic continuation of the group action)
    - Step 2: At Jost points (real spacelike configurations), local commutativity
      gives equality of values from different permuted tubes
    - Step 3: Edge-of-the-wedge theorem stitches adjacent permuted tubes together
    - Step 4: Iterate over all adjacent transpositions to cover all permutations -/
theorem bargmann_hall_wightman (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_lorentz : ∀ (Λ : LorentzGroup.Restricted (d := d))
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      -- At Jost points (spacelike real configurations), the boundary values from
      -- adjacent permuted tubes agree (this is local commutativity).
      -- When the difference x_{i+1} - x_i is spacelike, swapping positions i and i+1
      -- does not change the function value at real points.
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∃ (F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- F_ext is holomorphic on the permuted extended tube
      DifferentiableOn ℂ F_ext (PermutedExtendedTube d n) ∧
      -- F_ext restricts to F on the forward tube
      (∀ z ∈ ForwardTube d n, F_ext z = F z) ∧
      -- F_ext is invariant under the complex Lorentz group
      (∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = F_ext z) ∧
      -- F_ext is symmetric under permutations
      (∀ (π : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ PermutedExtendedTube d n →
        F_ext (fun k => z (π k)) = F_ext z) := by
  sorry

/-! ### Jost Points -/

/-- A Jost point is a real point in the extended forward tube.
    These exist when all (z_k - z_{k-1}) are spacelike.
    At Jost points, the Wightman function takes real (distributional) values,
    and local commutativity can be directly applied. -/
def IsJostPoint (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  z ∈ ComplexExtendedForwardTube d n ∧
  ∀ k : Fin n, ∀ μ : Fin (d + 1), (z k μ).im = 0

/-- At Jost points, all difference vectors are spacelike.
    This is Jost's lemma: if (x₁,...,xₙ) ∈ T'_n ∩ ℝ^{n(d+1)}, then
    (x_k - x_{k-1})² > 0 for all k. -/
theorem jost_lemma (z : Fin n → Fin (d + 1) → ℂ) (hz : IsJostPoint z) :
    ∀ k : Fin n, (k.val ≠ 0) →
    let prev := z ⟨k.val - 1, by omega⟩
    let diff : Fin (d + 1) → ℝ := fun μ => (z k μ).re - (prev μ).re
    MinkowskiSpace.minkowskiNormSq d diff > 0 := by
  sorry

/-! ### Schwinger Functions from Wightman Functions -/

/-- Define Schwinger functions from Wightman functions using analytic continuation.

    Given Wightman functions W_n with analytic continuation W_analytic to the forward tube,
    the Schwinger functions are defined by evaluating W_analytic at Euclidean points:

      S_n(τ₁, x⃗₁, ..., τₙ, x⃗ₙ) = W_analytic_n(iτ₁, x⃗₁, ..., iτₙ, x⃗ₙ)

    for τ₁ > τ₂ > ... > τₙ > 0 (time-ordered Euclidean points lie in the forward tube).

    By the BHW theorem, the analytic continuation extends to the permuted extended tube,
    making S_n well-defined and symmetric for all distinct Euclidean points. -/
def SchwingerFromWightman (d : ℕ) [NeZero d]
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ) :
    (n : ℕ) → (Fin n → Fin (d + 1) → ℝ) → ℂ :=
  fun n xs => W_analytic n (fun k => wickRotatePoint (xs k))

/-- The Schwinger functions defined from Wightman's analytic continuation are
    differentiable on the set of Euclidean configurations whose Wick-rotated
    images lie in the permuted extended tube.

    This follows from the chain rule: SchwingerFromWightman is the composition
    of the holomorphic W_analytic with the ℝ-linear Wick rotation map
    x ↦ (ix₀, x₁, ..., x_d), which is ℂ-differentiable. -/
theorem schwingerFromWightman_analytic
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW : ∀ n, DifferentiableOn ℂ (W_analytic n) (PermutedExtendedTube d n))
    (n : ℕ) :
    -- The Schwinger function is ℂ-differentiable on the preimage of the
    -- permuted extended tube under Wick rotation
    DifferentiableOn ℂ
      (fun xs : Fin n → Fin (d + 1) → ℂ =>
        W_analytic n (fun k => wickRotatePoint (fun μ => (xs k μ).re)))
      { xs | (fun k => wickRotatePoint (fun μ => (xs k μ).re)) ∈
          PermutedExtendedTube d n } := by
  sorry

/-! ### Temperedness of Schwinger Functions

The temperedness of Schwinger functions (OS axiom E0) requires bounding
|S_n(f)| for Schwartz test functions f. This follows from the temperedness
of Wightman functions (R0) together with the geometry of the Wick rotation.

OS I, Proposition 5.1 provides the key geometric estimate. -/

/-- The geometric domain Ω_n from OS I, Proposition 5.1.
    This is the set of Euclidean n-point configurations where the Wick-rotated
    points are "sufficiently inside" the forward tube for temperedness estimates. -/
def OmegaRegion (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℝ) :=
  { x | ∀ i j : Fin n, i ≠ j → x i ≠ x j }

/-! ### Key Properties for OS Axiom Verification -/

/-- Euclidean invariance of Schwinger functions follows from complex Lorentz
    invariance of the analytically continued Wightman functions.

    The key: SO(d+1) embeds into L₊(ℂ) as the subgroup of complex Lorentz
    transformations that preserve Euclidean points. Under the Wick rotation
    map (τ, x⃗) ↦ (iτ, x⃗), Euclidean rotations R ∈ SO(d+1) act as
    complex Lorentz transformations:

      R · (iτ, x⃗) = (i(Rτ), Rx⃗)    (viewing (τ, x⃗) as Euclidean coords)

    The complex Lorentz invariance of W_analytic on the permuted extended tube
    (from BHW) immediately gives SO(d+1) invariance of S_n. -/
theorem schwinger_euclidean_invariant
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_inv : ∀ n (Λ : ComplexLorentzGroup d) z,
      z ∈ PermutedExtendedTube d n →
      W_analytic n (fun k μ => ∑ ν, Λ.val μ ν * z k ν) = W_analytic n z)
    (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR_det : R.det = 1) (hR_orth : R.transpose * R = 1)
    (xs : Fin n → Fin (d + 1) → ℝ) :
    SchwingerFromWightman d W_analytic n (fun k => R.mulVec (xs k)) =
    SchwingerFromWightman d W_analytic n xs := by
  simp only [SchwingerFromWightman]
  -- Need: wickRotatePoint (R.mulVec x) = Λ_R · wickRotatePoint x
  -- where Λ_R = ComplexLorentzGroup.ofEuclidean R
  sorry

/-- Permutation symmetry of Schwinger functions follows from permutation symmetry
    of the BHW extension.

    BHW gives: W_analytic(z_{π(1)}, ..., z_{π(n)}) = W_analytic(z₁, ..., zₙ)
    for all z in the permuted extended tube.
    Restricting to Euclidean points gives S_n(x_{π(1)}, ..., x_{π(n)}) = S_n(x₁, ..., xₙ). -/
theorem schwinger_permutation_symmetric
    (W_analytic : (n : ℕ) → (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_perm : ∀ n (π : Equiv.Perm (Fin n)) z,
      z ∈ PermutedExtendedTube d n →
      W_analytic n (fun k => z (π k)) = W_analytic n z)
    (n : ℕ) (π : Equiv.Perm (Fin n)) (xs : Fin n → Fin (d + 1) → ℝ) :
    SchwingerFromWightman d W_analytic n (fun k => xs (π k)) =
    SchwingerFromWightman d W_analytic n xs := by
  simp only [SchwingerFromWightman]
  -- This requires: the Wick-rotated permuted points are in PermutedExtendedTube
  sorry

end

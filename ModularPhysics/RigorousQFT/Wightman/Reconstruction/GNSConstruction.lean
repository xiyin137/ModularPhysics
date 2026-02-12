/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.Wightman.Reconstruction

/-!
# GNS Construction for the Wightman Reconstruction Theorem

This file implements the Gelfand-Naimark-Segal (GNS) construction that builds
a Hilbert space and field operators from Wightman functions, completing the
Wightman reconstruction theorem.

## Construction Overview

Starting from Wightman functions W = {W_n : S(ℝ^{n(d+1)}) → ℂ} satisfying
the required axioms, the reconstruction proceeds as follows:

### Step 1: Borchers Algebra (already in Reconstruction.lean)
- Elements are "Borchers sequences" F = (f_0, f_1, f_2, ...) where f_n ∈ S(ℝ^{n(d+1)})
  and only finitely many f_n are nonzero
- This forms a *-algebra under:
  - Addition: (F + G)_n = f_n + g_n
  - Scalar multiplication: (cF)_n = c · f_n
  - *-operation (Borchers involution): (F*)_n(x₁,...,xₙ) = conj(f_n(xₙ,...,x₁))

### Step 2: Inner Product (already in Reconstruction.lean)
- ⟨F, G⟩ = Σ_{n,m} W_{n+m}(f*_n ⊗ g_m)
- Positive-definiteness from the Wightman positivity axiom
- Hermiticity from W_n(f̃) = conj(W_n(f)) and the Borchers involution
- Sesquilinearity from linearity of W_n

### Step 3: Null Space and Pre-Hilbert Space (already in Reconstruction.lean)
- N = {F : ⟨F,F⟩ = 0} is a left ideal (from Cauchy-Schwarz)
- PreHilbertSpace = BorchersSequence / N
- The inner product descends to the quotient (proven: well-definiteness)

### Step 4: Completion to Hilbert Space
- Complete the pre-Hilbert space using Mathlib's uniform completion
- The inner product extends by continuity

### Step 5: Field Operators
- For f ∈ S(ℝ^{d+1}), define φ(f) on Borchers sequences by:
    (φ(f)F)_n = δ_{n≥1} · f ⊗ f_{n-1}  (prepend f to the sequence)
- This preserves N, so descends to the pre-Hilbert space
- Extends to an unbounded operator on the Hilbert space (on a dense domain)

### Step 6: Vacuum
- Ω = equivalence class of (1, 0, 0, ...) (the sequence with f_0 = 1, rest zero)
- ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ) by construction

### Step 7: Verify Wightman Axioms
- Poincaré covariance: from translation invariance and Lorentz covariance of W_n
- Spectrum condition: from the spectral condition on W_n
- Locality: from local commutativity of W_n
- Cyclicity: from the density of Borchers sequences

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 3
* Wightman, "Quantum Field Theory in Terms of Vacuum Expectation Values" (1956)
* Borchers, "On Structure of the Algebra of Field Operators" (1962)
-/

noncomputable section

open Reconstruction

variable {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d)

/-! ### Step 4: Completion to Hilbert Space -/

/- The pre-inner product space structure on the Borchers quotient.

    This collects all the pieces proven in Reconstruction.lean:
    - The quotient type (PreHilbertSpace Wfn)
    - The inner product (PreHilbertSpace.innerProduct)
    - Sesquilinearity, positive semi-definiteness, hermiticity

    The completion gives the physical Hilbert space. -/

/-- The inner product on PreHilbertSpace is positive semi-definite with
    respect to the real part: Re⟨[F], [F]⟩ ≥ 0. -/
theorem preHilbert_inner_pos (F : PreHilbertSpace Wfn) :
    (PreHilbertSpace.innerProduct Wfn F F).re ≥ 0 := by
  -- The inner product on the quotient inherits positivity from BorchersSequence
  induction F using Quotient.inductionOn with
  | h a => exact Wfn.positive_definite a

/-- The inner product on PreHilbertSpace is actually real on the diagonal:
    ⟨[F], [F]⟩ ∈ ℝ (i.e., the imaginary part is zero). -/
theorem preHilbert_inner_real (F : PreHilbertSpace Wfn) :
    (PreHilbertSpace.innerProduct Wfn F F).im = 0 := by
  -- From hermiticity: ⟨F,F⟩ = conj(⟨F,F⟩), so ⟨F,F⟩ is real
  induction F using Quotient.inductionOn with
  | h a =>
    have hdef : PreHilbertSpace.innerProduct Wfn ⟦a⟧ ⟦a⟧ =
        WightmanInnerProduct d Wfn.W a a := rfl
    have herm := WightmanInnerProduct_hermitian Wfn a a
    have heq : starRingEnd ℂ (WightmanInnerProduct d Wfn.W a a) =
        WightmanInnerProduct d Wfn.W a a := herm.symm
    have him := congr_arg Complex.im heq
    simp [Complex.conj_im] at him
    linarith [congr_arg Complex.im hdef]

/-- The vacuum in PreHilbertSpace.
    Uses `Reconstruction.vacuumSequence` (f_0 = 1, f_n = 0 for n ≥ 1)
    defined in Reconstruction.lean. -/
def vacuumState : PreHilbertSpace Wfn :=
  Quotient.mk _ (vacuumSequence (d := d))

/-- The vacuum is normalized: ⟨Ω, Ω⟩ = W_0(1) = 1 -/
theorem vacuum_normalized :
    PreHilbertSpace.innerProduct Wfn (vacuumState Wfn) (vacuumState Wfn) = 1 := by
  -- Reduce quotient inner product to WightmanInnerProduct on representatives
  show WightmanInnerProduct d Wfn.W (vacuumSequence (d := d)) (vacuumSequence (d := d)) = 1
  -- Unfold the double sum: Σ_{n ∈ range 2} Σ_{m ∈ range 2} W(n+m)(Ω*_n ⊗ Ω_m)
  simp only [WightmanInnerProduct]
  -- Expand range(bound + 1) = range(2) into individual terms
  rw [show (vacuumSequence (d := d)).bound + 1 = 2 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- For n=1 or m=1: vacuumSequence.funcs 1 = 0
  have hv1 : (vacuumSequence (d := d)).funcs 1 = 0 := rfl
  simp only [hv1, SchwartzMap.conjTensorProduct_zero_left,
    SchwartzMap.conjTensorProduct_zero_right, (Wfn.linear _).map_zero, add_zero]
  -- Remaining: W(0+0)(f₀.conjTensorProduct f₀) = 1
  -- Simplify 0 + 0 to 0 and apply normalization: W 0 f = f 0
  show Wfn.W 0 (((vacuumSequence (d := d)).funcs 0).conjTensorProduct
    ((vacuumSequence (d := d)).funcs 0)) = 1
  rw [Wfn.normalized]
  -- Goal: (f₀.conjTensorProduct f₀) 0 = 1
  rw [SchwartzMap.conjTensorProduct_apply]
  -- vacuumSequence.funcs 0 is the constant 1 function, so all applications give 1
  have hconst : ∀ x, (vacuumSequence (d := d)).funcs 0 x = 1 := fun _ => rfl
  rw [hconst, hconst, map_one, one_mul]

/-! ### Step 5: Field Operators on Pre-Hilbert Space -/

/-- The field operator φ(f) maps null vectors to null vectors.

    If ⟨F, F⟩ = 0 then ⟨φ(f)F, φ(f)F⟩ = 0.

    Proof sketch: ⟨φ(f)F, φ(f)F⟩ = W₂(f̄ ⊗ f, F* ⊗ F) and the positivity
    condition implies this vanishes when F is null.

    More precisely, for any G: |⟨φ(f)F, G⟩|² ≤ ⟨φ(f)F, φ(f)F⟩ · ⟨G, G⟩.
    If F is null, then φ(f)F is also null. -/
theorem fieldOperator_preserves_null (f : SchwartzSpacetime d) (F : BorchersSequence d)
    (hF : (WightmanInnerProduct d Wfn.W F F).re = 0) :
    (WightmanInnerProduct d Wfn.W (fieldOperatorAction f F) (fieldOperatorAction f F)).re = 0 := by
  -- This requires showing that φ(f) maps null vectors to null vectors
  -- Key: ⟨φ(f)F, φ(f)F⟩ = W(F* · f* · f · F)
  -- and by Cauchy-Schwarz, this ≤ ⟨F, φ(f)*φ(f)F⟩ ≤ ...
  sorry

/-- The field operator well-definedness follows from preserving null vectors. -/
theorem fieldOperator_well_defined (f : SchwartzSpacetime d)
    (a b : BorchersSequence d) (hab : borchersSetoid Wfn a b) :
    borchersSetoid Wfn (fieldOperatorAction f a) (fieldOperatorAction f b) := by
  -- hab says ⟨a-b, a-b⟩.re = 0
  -- Need: ⟨φ(f)(a-b), φ(f)(a-b)⟩.re = 0
  -- φ(f) is linear on BorchersSequences, so φ(f)(a-b) = φ(f)a - φ(f)b
  -- Then apply fieldOperator_preserves_null
  sorry

/-! ### Step 6: The Key Property -/

/-- The fundamental property of the GNS construction:
    ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)

    This is what makes the reconstruction work — the matrix elements of the
    constructed field operators between vacuum states reproduce the original
    Wightman functions on product test functions.

    Proof: By induction on n.
    - Base case (n=0): ⟨Ω, Ω⟩ = W_0(1) = 1 (normalization)
    - Inductive step: φ(f) prepends f to the Borchers sequence, so
      φ(f₁)···φ(fₙ)Ω corresponds to the sequence with (n+k)-th component
      = f₁ ⊗ ··· ⊗ fₙ (in the (n+0)-th slot)
      and the inner product with Ω picks out W_n. -/
theorem gns_reproduces_wightman (n : ℕ) (fs : Fin n → SchwartzSpacetime d) :
    PreHilbertSpace.innerProduct Wfn (vacuumState Wfn)
      (List.foldr (fun f acc => fieldOperator Wfn f acc)
        (vacuumState Wfn) (List.ofFn fs)) =
    Wfn.W n (SchwartzMap.productTensor fs) := by
  sorry

/-! ### Step 7: Poincaré Covariance -/

/- The Poincaré group acts on Borchers sequences via the pull-back:
    (g · F)_n = F_n ∘ g⁻¹

    For the translation subgroup: (T_a · F)_n(x₁,...,xₙ) = F_n(x₁-a,...,xₙ-a)
    For the Lorentz subgroup: (Λ · F)_n(x₁,...,xₙ) = F_n(Λ⁻¹x₁,...,Λ⁻¹xₙ)

    This action preserves the inner product by translation/Lorentz invariance of W_n,
    and hence descends to a unitary representation on the Hilbert space. -/

/-- The translation action on Borchers sequences preserves the inner product.

    If F' and G' are the translations of F and G by a ∈ ℝ^{d+1}, meaning
    F'_n(x₁,...,xₙ) = F_n(x₁-a,...,xₙ-a), then ⟨F', G'⟩ = ⟨F, G⟩.

    Proof: Each summand W_{n+m}((f')*_n ⊗ g'_m) = W_{n+m}(f*_n ⊗ g_m) by
    the translation invariance of the Wightman functions. -/
theorem translation_preserves_inner (a : SpacetimeDim d)
    (F G F' G' : BorchersSequence d)
    (hF' : ∀ n (x : NPointDomain d n), (F'.funcs n) x = (F.funcs n) (fun i => x i - a))
    (hG' : ∀ n (x : NPointDomain d n), (G'.funcs n) x = (G.funcs n) (fun i => x i - a)) :
    WightmanInnerProduct d Wfn.W F' G' = WightmanInnerProduct d Wfn.W F G := by
  sorry

/-! ### Connecting Everything: The Full Reconstruction -/

/- Summary of what the Wightman reconstruction theorem proves:

    Given: WightmanFunctions d (satisfying temperedness, Poincaré covariance,
    spectrum condition, locality, positive-definiteness, hermiticity, normalization)

    Construct:
    1. Hilbert space H = completion of BorchersSequence / {null vectors}
    2. Vacuum Ω = [vacuumSequence] ∈ H, with ‖Ω‖ = 1
    3. Field operators φ(f) : H → H (unbounded, on dense domain)
    4. Unitary representation U of Poincaré group on H

    Properties:
    - ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)
    - U(g)Ω = Ω (vacuum is Poincaré-invariant)
    - U(g)φ(f)U(g)⁻¹ = φ(g·f) (covariance)
    - [φ(f), φ(g)] = 0 when supports of f, g are spacelike separated (locality)
    - Energy spectrum in forward cone (from spectrum condition)
    - span{φ(f₁)···φ(fₙ)Ω} is dense in H (cyclicity, from construction) -/

end

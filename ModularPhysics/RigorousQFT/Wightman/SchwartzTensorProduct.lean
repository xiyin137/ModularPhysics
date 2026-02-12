/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Tensor Products of Schwartz Functions

This file provides the external tensor product of Schwartz functions, which is
essential for the OS reconstruction theorem and the Wightman inner product.

## Main Definitions

* `SchwartzMap.tensorProduct` - The external tensor product f ⊗ g of Schwartz functions
* `SchwartzMap.conj` - Complex conjugation of a Schwartz function
* `SchwartzMap.conjTensorProduct` - The conjugated tensor product f̄ ⊗ g

## Mathematical Background

Given f ∈ S(ℝ^{m·d}, ℂ) and g ∈ S(ℝ^{k·d}, ℂ), the **external tensor product** is:
  (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(x_{m+1},...,x_{m+k})

This is a Schwartz function in S(ℝ^{(m+k)·d}, ℂ) because:
1. **Smoothness**: f and g are smooth, projections are smooth (linear), and multiplication
   of complex numbers is smooth (bilinear), so the composition is smooth.
2. **Rapid decay**: By the Leibniz rule for derivatives of products, each derivative of f⊗g
   is a sum of terms involving derivatives of f and g separately. The rapid decay of f and g
   on their respective variables gives rapid decay of f⊗g on all variables.

## References

* Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" (1973), §2-3
* Reed-Simon, "Methods of Modern Mathematical Physics I", §V.3
-/

noncomputable section

open scoped SchwartzMap
open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Complex Conjugation of Schwartz Functions -/

/-- Complex conjugation of a ℂ-valued Schwartz function.
    If f ∈ S(E, ℂ), then f̄ ∈ S(E, ℂ) where f̄(x) = conj(f(x)).

    This is well-defined because:
    1. conj : ℂ → ℂ is smooth (it's ℝ-linear)
    2. conj preserves norms: ‖conj(z)‖ = ‖z‖
    So f̄ has the same decay bounds as f. -/
def SchwartzMap.conj (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) where
  toFun := fun x => starRingEnd ℂ (f x)
  smooth' := by
    -- conj = starRingEnd ℂ is ℝ-linear and continuous, hence smooth
    -- The composition of smooth functions is smooth
    sorry
  decay' := by
    intro k n
    -- ‖conj(z)‖ = ‖z‖ for all z, and ‖iteratedFDeriv ℝ n (conj ∘ f) x‖ = ‖iteratedFDeriv ℝ n f x‖
    -- because conj is an isometric ℝ-linear map
    sorry

/-- Conjugation preserves the pointwise values. -/
@[simp]
theorem SchwartzMap.conj_apply (f : 𝓢(E, ℂ)) (x : E) :
    f.conj x = starRingEnd ℂ (f x) := rfl

/-- Conjugation is an involution. -/
theorem SchwartzMap.conj_conj (f : 𝓢(E, ℂ)) :
    f.conj.conj = f := by
  ext x
  simp [SchwartzMap.conj_apply]

/-! ### Argument Reversal for n-Point Functions -/

/-- Reversal of argument order for Schwartz functions on Fin n → E.
    Given f ∈ S(Fin n → E, ℂ), define f_rev(x₁,...,xₙ) = f(xₙ,...,x₁).

    This is well-defined because:
    1. (· ∘ Fin.rev) is a linear isomorphism on (Fin n → E)
    2. Composing a Schwartz function with a linear isomorphism is Schwartz -/
def SchwartzMap.reverse {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) : 𝓢(Fin n → E, ℂ) where
  toFun := fun x => f (fun i => x (Fin.rev i))
  smooth' := by
    -- (· ∘ Fin.rev) is an ℝ-linear isomorphism on (Fin n → E), hence smooth
    -- f is smooth, so f ∘ (· ∘ Fin.rev) is smooth
    sorry
  decay' := by
    -- (· ∘ Fin.rev) is a norm-preserving linear map (permutation of coordinates)
    -- so ‖x ∘ Fin.rev‖ = ‖x‖ and the decay bounds transfer directly
    sorry

/-- Reversal preserves pointwise values. -/
@[simp]
theorem SchwartzMap.reverse_apply {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) (x : Fin n → E) :
    f.reverse x = f (fun i => x (Fin.rev i)) := rfl

/-- Reversal is an involution. -/
theorem SchwartzMap.reverse_reverse {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    f.reverse.reverse = f := by
  ext x; simp [SchwartzMap.reverse_apply, Fin.rev_rev]

/-- Reversal of zero is zero. -/
@[simp]
theorem SchwartzMap.reverse_zero {n : ℕ} :
    (0 : 𝓢(Fin n → E, ℂ)).reverse = 0 := by
  ext x; simp [SchwartzMap.reverse_apply]

/-- Reversal distributes over addition. -/
@[simp]
theorem SchwartzMap.reverse_add {n : ℕ} (f g : 𝓢(Fin n → E, ℂ)) :
    (f + g).reverse = f.reverse + g.reverse := by
  ext x; simp [SchwartzMap.reverse_apply]

/-- Reversal distributes over negation. -/
@[simp]
theorem SchwartzMap.reverse_neg {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    (-f).reverse = -(f.reverse) := by
  ext x; simp [SchwartzMap.reverse_apply]

/-- Reversal commutes with scalar multiplication. -/
theorem SchwartzMap.reverse_smul {n : ℕ} (c : ℂ) (f : 𝓢(Fin n → E, ℂ)) :
    (c • f).reverse = c • f.reverse := by
  ext x; simp [SchwartzMap.reverse_apply]

/-! ### Borchers Conjugation (Involution) -/

/-- The Borchers conjugation (involution): reverse arguments and conjugate.
    f*(x₁,...,xₙ) = conj(f(xₙ,...,x₁))

    This is the adjoint operation in the Borchers algebra used to define the
    Wightman inner product: ⟨F, G⟩ = W(F⁺ × G) where F⁺ = (f₀*, f₁*, ...).

    Reference: Streater-Wightman, "PCT, Spin and Statistics", §3.4 -/
def SchwartzMap.borchersConj {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) : 𝓢(Fin n → E, ℂ) :=
  f.reverse.conj

/-- Borchers conjugation preserves pointwise values. -/
@[simp]
theorem SchwartzMap.borchersConj_apply {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) (x : Fin n → E) :
    f.borchersConj x = starRingEnd ℂ (f (fun i => x (Fin.rev i))) := rfl

/-- Borchers conjugation is an involution. -/
theorem SchwartzMap.borchersConj_borchersConj {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    f.borchersConj.borchersConj = f := by
  ext x; simp [SchwartzMap.borchersConj_apply, Fin.rev_rev]

/-- Borchers conjugation of zero is zero. -/
@[simp]
theorem SchwartzMap.borchersConj_zero {n : ℕ} :
    (0 : 𝓢(Fin n → E, ℂ)).borchersConj = 0 := by
  ext x; simp [SchwartzMap.borchersConj_apply]

/-- Borchers conjugation distributes over addition. -/
@[simp]
theorem SchwartzMap.borchersConj_add {n : ℕ} (f g : 𝓢(Fin n → E, ℂ)) :
    (f + g).borchersConj = f.borchersConj + g.borchersConj := by
  ext x; simp [SchwartzMap.borchersConj_apply, map_add]

/-- Borchers conjugation distributes over negation. -/
@[simp]
theorem SchwartzMap.borchersConj_neg {n : ℕ} (f : 𝓢(Fin n → E, ℂ)) :
    (-f).borchersConj = -(f.borchersConj) := by
  ext x; simp [SchwartzMap.borchersConj_apply, map_neg]

/-- Borchers conjugation is conjugate-linear in the scalar. -/
theorem SchwartzMap.borchersConj_smul {n : ℕ} (c : ℂ) (f : 𝓢(Fin n → E, ℂ)) :
    (c • f).borchersConj = starRingEnd ℂ c • f.borchersConj := by
  ext x; simp [SchwartzMap.borchersConj_apply, map_mul]

/-! ### External Tensor Product of Schwartz Functions -/

/-- The splitting map: given x : Fin (m+k) → E, extract the first m components.
    This sends x to (x₁, ..., xₘ). -/
def splitFirst (m k : ℕ) (x : Fin (m + k) → E) : Fin m → E :=
  fun i => x (Fin.castAdd k i)

/-- The splitting map: given x : Fin (m+k) → E, extract the last k components.
    This sends x to (x_{m+1}, ..., x_{m+k}). -/
def splitLast (m k : ℕ) (x : Fin (m + k) → E) : Fin k → E :=
  fun j => x (Fin.natAdd m j)

/-- splitFirst is a continuous linear map (projection). -/
theorem splitFirst_continuousLinear (m k : ℕ) :
    Continuous (splitFirst m k : (Fin (m + k) → E) → (Fin m → E)) :=
  continuous_pi fun i => continuous_apply _

/-- splitLast is a continuous linear map (projection). -/
theorem splitLast_continuousLinear (m k : ℕ) :
    Continuous (splitLast m k : (Fin (m + k) → E) → (Fin k → E)) :=
  continuous_pi fun j => continuous_apply _

/-- The external tensor product of two Schwartz functions.

    Given f ∈ S(Fin m → E, ℂ) and g ∈ S(Fin k → E, ℂ), define:
      (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(x_{m+1},...,x_{m+k})

    This is Schwartz because projections are smooth (linear), f and g are smooth,
    multiplication is smooth (bilinear), and the decay bounds combine. -/
def SchwartzMap.tensorProduct {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    𝓢(Fin (m + k) → E, ℂ) where
  toFun := fun x => f (splitFirst m k x) * g (splitLast m k x)
  smooth' := by
    -- f ∘ splitFirst is smooth (smooth ∘ linear)
    -- g ∘ splitLast is smooth (smooth ∘ linear)
    -- multiplication of smooth ℂ-valued functions is smooth
    sorry
  decay' := by
    -- By the Leibniz rule, ∂^n(f·g) = Σ C(n,j) (∂^j f)(∂^{n-j} g)
    -- Each term ‖x‖^k · ‖(∂^j f)(x_first)‖ · ‖(∂^{n-j} g)(x_last)‖
    -- is bounded using the individual decay of f and g, plus ‖x‖ ≥ max(‖x_first‖, ‖x_last‖)
    sorry

/-- The tensor product function at a point. -/
@[simp]
theorem SchwartzMap.tensorProduct_apply {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ))
    (x : Fin (m + k) → E) :
    f.tensorProduct g x = f (splitFirst m k x) * g (splitLast m k x) := rfl

/-- The Borchers conjugated tensor product: f* ⊗ g where f* is the Borchers involution.
    This is the pairing used in the Wightman inner product:
    ⟨F, G⟩ = Σ W_{n+m}(f*_n ⊗ g_m)
    where f*_n(x₁,...,xₙ) = conj(f_n(xₙ,...,x₁)).

    This is the CORRECT definition including argument reversal. The reversal is essential
    for the Hermiticity of the inner product: ⟨F, G⟩ = conj(⟨G, F⟩).

    Reference: Streater-Wightman, "PCT, Spin and Statistics", §3.4 -/
def SchwartzMap.conjTensorProduct {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    𝓢(Fin (m + k) → E, ℂ) :=
  f.borchersConj.tensorProduct g

@[simp]
theorem SchwartzMap.conjTensorProduct_apply {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ))
    (x : Fin (m + k) → E) :
    f.conjTensorProduct g x =
      starRingEnd ℂ (f (fun i => splitFirst m k x (Fin.rev i))) * g (splitLast m k x) := rfl

/-! ### Properties of the Tensor Product -/

/-- The tensor product is bilinear in the second argument. -/
theorem SchwartzMap.tensorProduct_add_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g₁ g₂ : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct (g₁ + g₂) = f.tensorProduct g₁ + f.tensorProduct g₂ := by
  ext x
  simp [mul_add]

/-- The tensor product is bilinear in the first argument. -/
theorem SchwartzMap.tensorProduct_add_left {m k : ℕ}
    (f₁ f₂ : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (f₁ + f₂).tensorProduct g = f₁.tensorProduct g + f₂.tensorProduct g := by
  ext x
  simp [add_mul]

/-- The tensor product with zero on the left is zero. -/
@[simp]
theorem SchwartzMap.tensorProduct_zero_left {m k : ℕ}
    (g : 𝓢(Fin k → E, ℂ)) :
    (0 : 𝓢(Fin m → E, ℂ)).tensorProduct g = 0 := by
  ext x; simp

/-- The tensor product with zero on the right is zero. -/
@[simp]
theorem SchwartzMap.tensorProduct_zero_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) :
    f.tensorProduct (0 : 𝓢(Fin k → E, ℂ)) = 0 := by
  ext x; simp

/-- Scalar multiplication distributes over tensor product. -/
theorem SchwartzMap.tensorProduct_smul_left {m k : ℕ}
    (c : ℂ) (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (c • f).tensorProduct g = c • (f.tensorProduct g) := by
  ext x
  simp [mul_assoc]

/-- The tensor product respects norms:
    ‖f ⊗ g‖_{k,l} ≤ C · ‖f‖_{k₁,l₁} · ‖g‖_{k₂,l₂}
    for appropriate seminorm indices. This is the key continuity bound. -/
theorem SchwartzMap.tensorProduct_continuous {m k : ℕ} :
    Continuous (fun p : 𝓢(Fin m → E, ℂ) × 𝓢(Fin k → E, ℂ) =>
      p.1.tensorProduct p.2) := by
  sorry

/-- Scalar multiplication distributes over tensor product (right). -/
theorem SchwartzMap.tensorProduct_smul_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (c : ℂ) (g : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct (c • g) = c • (f.tensorProduct g) := by
  ext x
  simp [mul_left_comm]

/-- Negation distributes over tensor product (left). -/
@[simp]
theorem SchwartzMap.tensorProduct_neg_left {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (-f).tensorProduct g = -(f.tensorProduct g) := by
  ext x; simp [neg_mul]

/-- Negation distributes over tensor product (right). -/
@[simp]
theorem SchwartzMap.tensorProduct_neg_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    f.tensorProduct (-g) = -(f.tensorProduct g) := by
  ext x; simp [mul_neg]

/-! ### Conjugation Algebra -/

/-- Conjugation of zero is zero. -/
@[simp]
theorem SchwartzMap.conj_zero : (0 : 𝓢(E, ℂ)).conj = 0 := by
  ext x; simp [SchwartzMap.conj_apply]

/-- Conjugation distributes over addition. -/
@[simp]
theorem SchwartzMap.conj_add (f g : 𝓢(E, ℂ)) : (f + g).conj = f.conj + g.conj := by
  ext x; simp [SchwartzMap.conj_apply, map_add]

/-- Conjugation distributes over negation. -/
@[simp]
theorem SchwartzMap.conj_neg (f : 𝓢(E, ℂ)) : (-f).conj = -(f.conj) := by
  ext x; simp [SchwartzMap.conj_apply, map_neg]

/-- Conjugation interacts with scalar multiplication via conjugation of the scalar. -/
theorem SchwartzMap.conj_smul (c : ℂ) (f : 𝓢(E, ℂ)) :
    (c • f).conj = starRingEnd ℂ c • f.conj := by
  ext x; simp [SchwartzMap.conj_apply, map_mul]

/-! ### Conjugated Tensor Product Algebra -/

/-- Conjugated tensor product with zero on the left is zero. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_zero_left {m k : ℕ}
    (g : 𝓢(Fin k → E, ℂ)) :
    (0 : 𝓢(Fin m → E, ℂ)).conjTensorProduct g = 0 := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product with zero on the right is zero. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_zero_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) :
    f.conjTensorProduct (0 : 𝓢(Fin k → E, ℂ)) = 0 := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product is additive in the second argument. -/
theorem SchwartzMap.conjTensorProduct_add_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g₁ g₂ : 𝓢(Fin k → E, ℂ)) :
    f.conjTensorProduct (g₁ + g₂) = f.conjTensorProduct g₁ + f.conjTensorProduct g₂ := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.tensorProduct_add_right]

/-- Conjugated tensor product is additive in the first argument. -/
theorem SchwartzMap.conjTensorProduct_add_left {m k : ℕ}
    (f₁ f₂ : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (f₁ + f₂).conjTensorProduct g = f₁.conjTensorProduct g + f₂.conjTensorProduct g := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.tensorProduct_add_left]

/-- Conjugated tensor product: negation in the first argument. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_neg_left {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (-f).conjTensorProduct g = -(f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product: negation in the second argument. -/
@[simp]
theorem SchwartzMap.conjTensorProduct_neg_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    f.conjTensorProduct (-g) = -(f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct]

/-- Conjugated tensor product: scalar multiplication in the second argument. -/
theorem SchwartzMap.conjTensorProduct_smul_right {m k : ℕ}
    (f : 𝓢(Fin m → E, ℂ)) (c : ℂ) (g : 𝓢(Fin k → E, ℂ)) :
    f.conjTensorProduct (c • g) = c • (f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.tensorProduct_smul_right]

/-- Conjugated tensor product: scalar multiplication in the first argument.
    Uses conjugation: conj(c·f) ⊗ g = c̄ · (conj(f) ⊗ g) -/
theorem SchwartzMap.conjTensorProduct_smul_left {m k : ℕ}
    (c : ℂ) (f : 𝓢(Fin m → E, ℂ)) (g : 𝓢(Fin k → E, ℂ)) :
    (c • f).conjTensorProduct g = starRingEnd ℂ c • (f.conjTensorProduct g) := by
  simp [SchwartzMap.conjTensorProduct, SchwartzMap.borchersConj_smul,
    SchwartzMap.tensorProduct_smul_left]

/-! ### Prepend Operation -/

/-- Prepend a single-variable Schwartz function to an n-point Schwartz function.
    (prepend f g)(x₀, x₁,...,xₙ) = f(x₀) · g(x₁,...,xₙ)

    This returns `𝓢(Fin (n + 1) → E, ℂ)` directly, avoiding the `Fin (1 + n)` vs
    `Fin (n + 1)` definitional equality issue that arises with `tensorProduct`. -/
def SchwartzMap.prependField {n : ℕ}
    (f : 𝓢(E, ℂ)) (g : 𝓢(Fin n → E, ℂ)) : 𝓢(Fin (n + 1) → E, ℂ) where
  toFun := fun x => f (x 0) * g (fun i => x i.succ)
  smooth' := by
    -- x ↦ x 0 is a continuous linear projection, hence smooth
    -- x ↦ (fun i => x i.succ) is a continuous linear map, hence smooth
    -- f and g are smooth, and multiplication is smooth (bilinear)
    sorry
  decay' := by
    -- Decay of f in x₀ and g in (x₁,...,xₙ), combined with ‖x‖ ≥ max(‖x₀‖, ‖x_rest‖)
    sorry

@[simp]
theorem SchwartzMap.prependField_apply {n : ℕ}
    (f : 𝓢(E, ℂ)) (g : 𝓢(Fin n → E, ℂ)) (x : Fin (n + 1) → E) :
    f.prependField g x = f (x 0) * g (fun i => x i.succ) := rfl

@[simp]
theorem SchwartzMap.prependField_zero_right {n : ℕ}
    (f : 𝓢(E, ℂ)) :
    f.prependField (0 : 𝓢(Fin n → E, ℂ)) = 0 := by
  ext x; simp

@[simp]
theorem SchwartzMap.prependField_zero_left {n : ℕ}
    (g : 𝓢(Fin n → E, ℂ)) :
    (0 : 𝓢(E, ℂ)).prependField g = 0 := by
  ext x; simp

theorem SchwartzMap.prependField_add_right {n : ℕ}
    (f : 𝓢(E, ℂ)) (g₁ g₂ : 𝓢(Fin n → E, ℂ)) :
    f.prependField (g₁ + g₂) = f.prependField g₁ + f.prependField g₂ := by
  ext x; simp [mul_add]

/-! ### Splitting and Appending -/

/-- splitFirst ∘ Fin.append extracts the first component. -/
@[simp]
theorem splitFirst_append {α : Type*} {m k : ℕ}
    (f : Fin m → α) (g : Fin k → α) :
    splitFirst m k (Fin.append f g) = f := by
  ext i
  simp [splitFirst, Fin.append_left]

/-- splitLast ∘ Fin.append extracts the second component. -/
@[simp]
theorem splitLast_append {α : Type*} {m k : ℕ}
    (f : Fin m → α) (g : Fin k → α) :
    splitLast m k (Fin.append f g) = g := by
  ext j
  simp [splitLast, Fin.append_right]

end

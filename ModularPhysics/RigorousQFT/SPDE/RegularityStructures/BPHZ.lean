/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.RegularityStructures.FixedPoint

/-!
# BPHZ Renormalization for Regularity Structures

This file formalizes the BPHZ (Bogoliubov-Parasiuk-Hepp-Zimmermann) renormalization
procedure for regularity structures (Hairer 2014, Section 8).

## Main Definitions

* `RenormalizationGroupRS` - The renormalization group acting on models
* `BPHZCharacter` - The BPHZ character computing renormalization constants
* `RenormalizedModel` - The renormalized model Π^{ren}

## Mathematical Background

The BPHZ procedure in regularity structures works as follows:

1. **Identify divergent trees**: Trees τ with |τ| < 0 have divergent expectations
2. **Renormalization group**: G acts on models by Π_x^g τ = Π_x (g · τ)
3. **BPHZ formula**: The renormalization element g ∈ G is computed recursively
   by subtracting divergences from each tree

The key insight (connecting to classical QFT renormalization) is that:
- Trees correspond to Feynman diagrams
- Negative homogeneity corresponds to UV divergence
- The recursive BPHZ formula is the same as in perturbative QFT

Unlike the BHZ (Bruned-Hairer-Zambotti) approach using Hopf algebras, we use
the direct recursive formula from Hairer 2014.

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 8
* Bruned, Hairer, Zambotti, "Algebraic renormalisation of regularity structures" (2019)
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## The Renormalization Group

The structure group G acts on models. Renormalization is achieved by
choosing the right element g ∈ G such that Π^g has finite limits.
-/

/-- The renormalization group for a regularity structure.

    Elements M ∈ G are linear maps M : T → T such that:
    - M preserves the unit: M(1) ≡ 1 (up to coefficient equivalence)
    - M preserves homogeneity sectors: M(T_α) ⊆ ⊕_{β ≤ α} T_β
    - M acts triangularly: (M τ)_α = τ_α + lower order terms

    The group operation is composition. -/
structure RenormGroupElement (d : ℕ) where
  /-- The linear map M : T → T -/
  M : TreeSymbol d → FormalSum d
  /-- Unit preservation (coefficient form): M(1) has coefficient 1 at 1, and 0 elsewhere.
      This is equivalent to M(1) ≡ 1 for evaluation purposes. -/
  unit_preserved_coeff : (M .one).coeff .one = 1
  unit_preserved_other : ∀ τ : TreeSymbol d, τ ≠ .one → (M .one).coeff τ = 0
  /-- Triangularity: The coefficient of τ in M(τ) is 1.
      This means M(τ) = τ + (lower order terms). -/
  triangular : ∀ τ : TreeSymbol d, (M τ).coeff τ = 1

namespace RenormGroupElement

variable {d : ℕ}

/-- The identity element -/
def one : RenormGroupElement d where
  M := fun τ => FormalSum.single τ
  unit_preserved_coeff := FormalSum.coeff_single_self .one
  unit_preserved_other := fun τ hτ => FormalSum.coeff_single_ne .one τ hτ
  triangular := fun τ => FormalSum.coeff_single_self τ

/-- Composition of renormalization group elements.
    (g * h).M(τ) = g.M applied linearly to h.M(τ)
    If h.M(τ) = Σᵢ cᵢ σᵢ, then (g * h).M(τ) = Σᵢ cᵢ · g.M(σᵢ) -/
noncomputable def mul (g h : RenormGroupElement d) : RenormGroupElement d where
  M := fun τ => FormalSum.bind (h.M τ) g.M
  unit_preserved_coeff := by
    -- (g * h).M(.one) = bind (h.M .one) g.M
    -- Need: coeff .one (bind (h.M .one) g.M) = 1
    -- h.M .one has coeff 1 at .one and 0 elsewhere
    -- By coeff_bind_unit_like, result = (g.M .one).coeff .one = 1
    rw [FormalSum.coeff_bind_unit_like (h.M .one) g.M .one .one
        h.unit_preserved_coeff h.unit_preserved_other]
    exact g.unit_preserved_coeff
  unit_preserved_other := fun τ hτ => by
    -- coeff τ (bind (h.M .one) g.M) = 0 for τ ≠ .one
    -- By coeff_bind_unit_like, result = (g.M .one).coeff τ = 0 (by g.unit_preserved_other)
    rw [FormalSum.coeff_bind_unit_like (h.M .one) g.M .one τ
        h.unit_preserved_coeff h.unit_preserved_other]
    exact g.unit_preserved_other τ hτ
  triangular := fun τ => by
    -- Need: (bind (h.M τ) g.M).coeff τ = 1
    -- This is more subtle: h.M τ has coeff 1 at τ, but may have non-zero coeffs at other trees
    -- The bind computes: Σ_σ (h.M τ).coeff σ * (g.M σ).coeff τ
    -- = (h.M τ).coeff τ * (g.M τ).coeff τ + Σ_{σ≠τ} (h.M τ).coeff σ * (g.M σ).coeff τ
    -- = 1 * 1 + Σ_{σ≠τ} (h.M τ).coeff σ * (g.M σ).coeff τ
    -- For this to equal 1, we need the sum over σ ≠ τ to be 0
    -- This requires additional structure (e.g., triangularity in the grading sense)
    -- For now, mark as sorry as this needs more constraints on RenormGroupElement
    sorry

/-- The lower-order part of a renormalization group element.
    If M(τ) = τ + L(τ), returns L(τ). -/
noncomputable def lowerOrderPart (g : RenormGroupElement d) (τ : TreeSymbol d) : FormalSum d :=
  g.M τ - FormalSum.single τ

/-- Apply the lower-order part n times (L^n) -/
noncomputable def lowerOrderPower (g : RenormGroupElement d) : ℕ → TreeSymbol d → FormalSum d
  | 0, τ => FormalSum.single τ
  | n + 1, τ => FormalSum.bind (lowerOrderPower g n τ) (lowerOrderPart g)

/-- Inverse element using Neumann series truncated at complexity bound.
    For a triangular operator M(τ) = τ + L(τ) where L has strictly lower homogeneity,
    the inverse is M⁻¹ = Id - L + L² - L³ + ... (Neumann series).
    Since L is nilpotent on finite-complexity trees, this terminates.

    We truncate at n = complexity(τ) + 1 since L^n(τ) = 0 for n > complexity(τ). -/
noncomputable def inv (g : RenormGroupElement d) : RenormGroupElement d where
  M := fun τ =>
    -- M⁻¹(τ) = Σₙ (-1)^n L^n(τ)
    -- Truncate at complexity(τ) + 1
    let bound := τ.complexity + 1
    (List.range bound).foldl
      (fun acc n =>
        acc + (if n % 2 = 0 then (1 : ℝ) else (-1 : ℝ)) • lowerOrderPower g n τ)
      FormalSum.zero
  unit_preserved_coeff := by
    -- For τ = .one, complexity = 1, so bound = 2
    -- The n=0 term gives coeff 1 at .one, higher terms contribute 0
    sorry  -- Requires detailed foldl analysis
  unit_preserved_other := fun τ hτ => by
    -- For τ ≠ .one, coeff τ in inv.M(.one) = 0
    sorry  -- Requires detailed foldl analysis
  triangular := fun τ => by
    -- The n=0 term is L^0(τ) = single τ with coefficient 1
    -- Higher n terms: L^n(τ) for n ≥ 1 has coeff 0 at τ (L lowers homogeneity)
    -- So total coeff at τ is 1*1 = 1
    -- Full proof requires lemmas about coeff, smul, foldl interaction
    sorry

instance : One (RenormGroupElement d) := ⟨one⟩
noncomputable instance : Mul (RenormGroupElement d) := ⟨mul⟩
noncomputable instance : Inv (RenormGroupElement d) := ⟨inv⟩

/-- Right identity: g * 1 = g -/
theorem mul_one (g : RenormGroupElement d) : mul g one = g := by
  simp only [mul, one]
  -- (mul g one).M τ = bind (one.M τ) g.M = bind (single τ) g.M
  -- We need: bind (single τ) g.M = g.M τ
  congr 1
  ext τ
  exact FormalSum.bind_single τ g.M

/-- Left identity: 1 * g = g -/
theorem one_mul (g : RenormGroupElement d) : mul one g = g := by
  simp only [mul, one]
  -- (mul one g).M τ = bind (g.M τ) one.M = bind (g.M τ) single
  -- We need: bind (g.M τ) single = g.M τ
  congr 1
  ext τ
  exact FormalSum.bind_single_right (g.M τ)

end RenormGroupElement

/-! ## Action of G on Models

The renormalization group acts on models by:
  Π^g_x τ = Π_x (g · τ)

This changes the model while preserving its analytical structure.
-/

/-- Evaluate a FormalSum using a model's pairing function.
    For s = Σᵢ cᵢ τᵢ, returns Σᵢ cᵢ · ⟨Π_x τᵢ, φ^λ_x⟩ -/
noncomputable def evalFormalSum {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (s : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) : ℝ :=
  s.terms.foldl (fun acc (c, τ) => acc + c * model.Pi.pairing τ x φ scale) 0

/-- Evaluation of single gives the pairing value -/
theorem evalFormalSum_single {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (τ : TreeSymbol d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    evalFormalSum model (FormalSum.single τ) x φ scale = model.Pi.pairing τ x φ scale := by
  simp only [evalFormalSum, FormalSum.single, List.foldl_cons, List.foldl_nil]
  ring

/-- Helper: the eval foldl function is shift-invariant -/
private theorem evalFoldl_shift {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ)
    (l : List (ℝ × TreeSymbol d)) (init : ℝ) :
    l.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * model.Pi.pairing p.2 x φ scale) init =
    init + l.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * model.Pi.pairing p.2 x φ scale) 0 := by
  induction l generalizing init with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.foldl_cons]
    rw [ih (init + hd.1 * model.Pi.pairing hd.2 x φ scale)]
    rw [ih (0 + hd.1 * model.Pi.pairing hd.2 x φ scale)]
    ring

/-- Evaluation distributes over addition -/
theorem evalFormalSum_add {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (s₁ s₂ : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    evalFormalSum model (s₁ + s₂) x φ scale =
    evalFormalSum model s₁ x φ scale + evalFormalSum model s₂ x φ scale := by
  unfold evalFormalSum
  show (s₁ + s₂).terms.foldl _ 0 = s₁.terms.foldl _ 0 + s₂.terms.foldl _ 0
  have heq : (s₁ + s₂).terms = s₁.terms ++ s₂.terms := rfl
  rw [heq, List.foldl_append]
  rw [evalFoldl_shift]

/-- Evaluation of scalar multiple -/
theorem evalFormalSum_smul {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (c : ℝ) (s : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    evalFormalSum model (c • s) x φ scale = c * evalFormalSum model s x φ scale := by
  unfold evalFormalSum
  have heq : (c • s).terms = s.terms.map (fun (a, τ) => (c * a, τ)) := rfl
  rw [heq]
  induction s.terms with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [evalFoldl_shift _ _ _ _ _ (0 + c * hd.1 * _)]
    rw [evalFoldl_shift _ _ _ _ _ (0 + hd.1 * _)]
    rw [ih]
    ring

/-- The action of the renormalization group on models.

    Given g ∈ G and a model (Π, Γ), the renormalized model is:
    - Π^g_x τ = Π_x (M_g · τ)  (evaluate g.M(τ) using the original model)
    - Γ^g_{xy} = M_g ∘ Γ_{xy} ∘ M_g⁻¹  (composition of linear maps)

    For the Gamma action, since all maps are linear:
    - First apply g⁻¹ to τ: g.inv.M τ gives a FormalSum
    - Then apply original Γ_{xy} to each tree in the sum (via bind)
    - Then apply g to the result (via bind)

    Reference: Hairer 2014, Section 8 -/
noncomputable def renormAction {d : ℕ} {params : ModelParameters d}
    (g : RenormGroupElement d) (model : AdmissibleModel d params) :
    AdmissibleModel d params where
  Pi := {
    pairing := fun τ x φ scale =>
      -- Π^g_x τ = Σᵢ cᵢ · ⟨Π_x σᵢ, φ⟩ where g.M(τ) = Σᵢ cᵢ σᵢ
      evalFormalSum model (g.M τ) x φ scale
    unit_property := fun x φ scale hs_pos hs_le => by
      -- evalFormalSum model (g.M .one) x φ scale = 1
      -- Using: g.unit_preserved_coeff : (g.M .one).coeff .one = 1
      --        g.unit_preserved_other : ∀ τ ≠ .one, (g.M .one).coeff τ = 0
      --        model.Pi.unit_property : model.Pi.pairing .one x φ scale = 1
      -- The proof requires showing evalFormalSum respects coefficient structure
      -- This needs infrastructure connecting coeff and evalFormalSum
      sorry
  }
  Gamma := {
    Gamma := fun x y τ =>
      -- Γ^g_{xy}(τ) = M_g(Γ_{xy}(M_g⁻¹(τ)))
      -- Step 1: Apply g⁻¹ to τ to get g.inv.M τ : FormalSum d
      -- Step 2: Extend Γ_{xy} to FormalSum by linearity (via bind)
      -- Step 3: Apply g.M to the result (via bind)
      let invApplied := g.inv.M τ                            -- FormalSum d
      let gammaApplied := FormalSum.bind invApplied (model.Gamma.Gamma x y)  -- FormalSum d
      FormalSum.bind gammaApplied g.M                        -- FormalSum d
    self_eq_id := fun x τ => by
      -- Need: bind (bind (g.inv.M τ) (Γ_xx)) g.M = single τ
      -- Since Γ_xx τ = single τ (identity), and g * g⁻¹ = id
      -- First unfold the let bindings
      simp only []
      -- Step 1: bind (g.inv.M τ) (Γ_xx) = bind (g.inv.M τ) single = g.inv.M τ
      have h1 : FormalSum.bind (g.inv.M τ) (model.Gamma.Gamma x x) =
                FormalSum.bind (g.inv.M τ) FormalSum.single := by
        congr 1
        ext σ
        exact model.Gamma.self_eq_id x σ
      rw [h1, FormalSum.bind_single_right]
      -- Need: bind (g.inv.M τ) g.M = single τ
      -- This is g * g⁻¹ = id applied to τ
      sorry  -- Requires: mul g (inv g) = one, i.e., g * g⁻¹ = id
    cocycle := fun x y z τ => by
      -- Cocycle condition: bind (bind (inv τ) (Γ_yz)) g.M composed with Γ_xy
      -- equals direct Γ_xz application
      -- This follows from the cocycle property of the original Γ
      sorry  -- Requires careful tracking of compositions
  }
  bound_const := model.bound_const
  bound_pos := model.bound_pos
  regularity_index := model.regularity_index
  analytical_bound := sorry  -- Renormalized model still satisfies bounds
  consistency := sorry

/-! ## Trees Requiring Renormalization

A tree τ requires renormalization if |τ| < 0. For such trees, the
naive model Π_x τ has divergent expectations that must be subtracted.
-/

/-- The set of trees requiring renormalization at level n.
    These are trees with:
    - Negative homogeneity: |τ| < 0
    - Complexity at most n -/
def treesRequiringRenorm (d : ℕ) (params : ModelParameters d) (n : ℕ) :
    Set (TreeSymbol d) :=
  { τ | τ.complexity ≤ n ∧
        homogeneity params.noiseRegularity params.kernelOrder τ < 0 }

/-! ## The BPHZ Character

The BPHZ character computes the renormalization constants recursively.
For each tree τ with |τ| < 0, we compute the counterterm:

  g_τ = -E[Π^{ren}_x τ] + (lower order corrections)

This is the direct approach from Hairer 2014, without Hopf algebras.
-/

/-- The BPHZ character g : T → ℝ.

    For each tree τ, g(τ) is the renormalization constant. The character
    is computed recursively:
    - g(1) = 0 (unit needs no renormalization)
    - g(Ξ) = 0 (noise is already normalized)
    - g(X^k) = 0 (polynomials need no renormalization)
    - g(τ) = -E[Π_0 τ] + (recursive corrections) for |τ| < 0 -/
structure BPHZCharacter (d : ℕ) (params : ModelParameters d) where
  /-- The character value g(τ) for each tree -/
  g : TreeSymbol d → ℝ
  /-- Unit: g(1) = 0 -/
  unit_zero : g .one = 0
  /-- Noise: g(Ξ) = 0 -/
  noise_zero : g .Xi = 0
  /-- Polynomial: g(X^k) = 0 -/
  poly_zero : ∀ k : MultiIndex d, g (.Poly k) = 0
  /-- Subcritical trees: g(τ) = 0 when |τ| ≥ 0 -/
  subcritical_zero : ∀ τ : TreeSymbol d,
    homogeneity params.noiseRegularity params.kernelOrder τ ≥ 0 → g τ = 0

namespace BPHZCharacter

variable {d : ℕ} {params : ModelParameters d}

/-- The renormalization element in G induced by the BPHZ character.
    This element g ∈ G is defined by M_g τ = τ + g(τ) · 1 -/
noncomputable def toGroupElement (char : BPHZCharacter d params) : RenormGroupElement d where
  M := fun τ => FormalSum.single τ + (char.g τ) • FormalSum.single .one
  unit_preserved_coeff := by
    -- coeff .one (single .one + g(.one) • single .one)
    -- = coeff .one (single .one) + g(.one) * coeff .one (single .one)
    -- = 1 + 0 * 1 = 1 (since char.unit_zero)
    rw [FormalSum.coeff_add, FormalSum.coeff_smul, FormalSum.coeff_single_self,
        char.unit_zero]
    ring
  unit_preserved_other := fun τ hτ => by
    -- coeff τ (single .one + g(.one) • single .one) = 0 for τ ≠ .one
    rw [FormalSum.coeff_add, FormalSum.coeff_smul,
        FormalSum.coeff_single_ne .one τ hτ]
    ring
  triangular := fun τ => by
    -- coeff τ (single τ + g(τ) • single 1) = coeff τ (single τ) + coeff τ (g(τ) • single 1)
    rw [FormalSum.coeff_add, FormalSum.coeff_smul, FormalSum.coeff_single_self]
    -- = 1 + g(τ) * coeff τ (single 1)
    by_cases hτ : τ = .one
    · -- τ = 1: coeff 1 (single 1) = 1, but char.g 1 = 0
      subst hτ
      rw [FormalSum.coeff_single_self, char.unit_zero]
      ring
    · -- τ ≠ 1: coeff τ (single 1) = 0
      rw [FormalSum.coeff_single_ne .one τ hτ]
      ring

end BPHZCharacter

/-! ## The Renormalized Model

The BPHZ renormalization produces a model Π^{ren} that:
1. Agrees with Π on subcritical trees (|τ| ≥ 0)
2. Has finite limits on critical trees (|τ| < 0)
3. Is universal: independent of the mollification

This is Theorem 8.3 from Hairer 2014.
-/

/-- The renormalized model Π^{ren} = Π^g where g is the BPHZ element.

    Key properties:
    - Π^{ren}_x τ = Π_x τ for subcritical τ
    - E[Π^{ren}_x τ] = 0 for critical τ (divergences subtracted)
    - Π^{ren} has a finite limit as ε → 0 -/
noncomputable def renormalizedModel {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params)
    (char : BPHZCharacter d params) : AdmissibleModel d params :=
  renormAction (char.toGroupElement) model

/-- The BPHZ renormalization theorem (Hairer 2014, Theorem 8.3).

    For the canonical model Π^ε built from mollified noise ξ_ε:
    1. There exists a BPHZ character g_ε
    2. The renormalized model Π^{ε,ren} = Π^{ε,g_ε} has a limit as ε → 0
    3. The limit is independent of the mollification (universality) -/
theorem bphz_renormalization {d : ℕ} {params : ModelParameters d}
    (data : CanonicalModelData d params) (γ : ℝ) (hγ : γ > 0) :
    -- For each ε > 0, there exists a BPHZ character
    ∀ ε > 0, ∃ char_ε : BPHZCharacter d params,
    -- Such that the renormalized models converge
    ∃ model_limit : AdmissibleModel d params,
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε' : ℝ, ∀ hε' : 0 < ε', ε' < ε₀ →
      -- The distance between renormalized model and limit is less than δ
      AdmissibleModel.distance (renormalizedModel (canonical_model data ε' hε') char_ε) model_limit γ < δ := by
  sorry  -- This is the main renormalization theorem

/-! ## Explicit BPHZ Formula

The BPHZ character is computed recursively. For a tree τ with |τ| < 0:

  g(τ) = -E[Π_0(τ - Σ_{σ ⊂ τ, |σ| < 0} g(σ) · τ/σ)]

where the sum is over divergent subtrees σ of τ, and τ/σ denotes the
contraction of σ in τ.
-/

/-- The recursive BPHZ formula for the character.

    For a tree τ with |τ| < 0:
    g(τ) = -E[Π_0(τ)] + (sum over divergent subtrees)

    This is computed recursively in order of increasing complexity.
    The key property is that g(τ) depends only on g(σ) for subtrees σ ⊊ τ
    with |σ| < 0 (divergent proper subtrees). -/
theorem bphz_recursive_formula {d : ℕ} {params : ModelParameters d}
    (char : BPHZCharacter d params)
    (τ : TreeSymbol d)
    (hτ : homogeneity params.noiseRegularity params.kernelOrder τ < 0) :
    -- The BPHZ character g(τ) is determined by a recursive formula
    -- involving only trees of strictly smaller complexity
    ∀ τ' : TreeSymbol d,
      τ'.complexity < τ.complexity →
      homogeneity params.noiseRegularity params.kernelOrder τ' < 0 →
      -- The character at τ depends on characters at smaller trees
      -- This expresses the recursive structure of BPHZ renormalization
      |char.g τ| ≤ |char.g τ'| + τ.complexity := by
  sorry  -- Requires subtree enumeration and recursive bound analysis

/-! ## Φ⁴₃ Renormalization

For the 3D Φ⁴ model, the trees requiring renormalization are:
- I(Ξ)² with |τ| = -1
- I(Ξ)³ with |τ| = -3/2
- I(I(Ξ)² · Ξ) with |τ| = -1/2

Each gives a divergent counterterm (mass renormalization).
-/

/-- The renormalization constants for Φ⁴₃.

    The key divergent trees are:
    - τ₁ = I(Ξ)² : gives mass counterterm δm²
    - τ₂ = I(Ξ)³ : finite in 3D
    - τ₃ = I(I(Ξ)² · Ξ) : gives coupling counterterm -/
structure Phi4RenormConstants where
  /-- Mass counterterm δm²(ε) -/
  mass_counterterm : ℝ → ℝ
  /-- Logarithmic divergence coefficient -/
  log_coeff : ℝ
  /-- Logarithmic divergence: |δm²(ε) - c log(1/ε)| is bounded as ε → 0 -/
  log_divergence : ∃ M : ℝ, ∀ ε > 0,
    |mass_counterterm ε - log_coeff * Real.log (1/ε)| ≤ M
  /-- Coupling counterterm (finite in 3D) -/
  coupling_counterterm : ℝ → ℝ
  /-- Coupling has a finite limit -/
  coupling_finite : ∃ limit : ℝ, Filter.Tendsto coupling_counterterm
    (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)

/-! ## KPZ Renormalization

For the KPZ equation in 1D, the divergent tree is I(∂I(Ξ))²
corresponding to the (∇h)² nonlinearity. The renormalization
gives a single divergent constant (energy counterterm).
-/

/-- The renormalization constants for KPZ.

    The key divergent tree is τ = I((∂I(Ξ))²) with |τ| = 0.
    This is at the boundary and requires a single counterterm. -/
structure KPZRenormConstants where
  /-- The counterterm C(ε) -/
  counterterm : ℝ → ℝ
  /-- Linear divergence coefficient -/
  linear_coeff : ℝ
  /-- Linear divergence: |C(ε) - c/ε| is bounded as ε → 0 -/
  linear_divergence : ∃ M : ℝ, ∀ ε > 0,
    |counterterm ε - linear_coeff / ε| ≤ M

end SPDE.RegularityStructures

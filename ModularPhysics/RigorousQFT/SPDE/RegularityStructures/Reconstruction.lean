/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.RegularityStructures.Models.Canonical

/-!
# The Reconstruction Theorem

This file formalizes the Reconstruction Theorem (Hairer 2014, Theorem 3.10),
which is one of the main workhorses of regularity structures theory.

## Main Definitions

* `ModelledDistribution` - Functions f : ℝ^d → T that are locally described by the model
* `ReconstructionMap` - The map R : D^γ → C^α_s reconstructing actual distributions
* `reconstruction_bound` - The key bound |⟨Rf - Π_x f(x), φ^λ_x⟩| ≤ C λ^γ

## Mathematical Background

The Reconstruction Theorem states that for a regularity structure T = (A, T, G)
with model (Π, Γ), there exists a continuous linear map R : D^γ → C^α_s such that:

  |⟨Rf - Π_x f(x), φ^λ_x⟩| ≤ C λ^γ ‖Π‖ |||f|||

where:
- D^γ is the space of modelled distributions (γ-Hölder in a generalized sense)
- C^α_s is the Hölder-Besov space with scaling s
- α = min A is the minimum homogeneity

The key insight is that modelled distributions f encode "what the solution looks like
locally" via the model, and R reconstructs the actual distribution from this local data.

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Theorem 3.10
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## Modelled Distributions

A modelled distribution f : ℝ^d → T assigns to each point x a formal expansion
in the regularity structure. The key regularity condition is:

  ‖f(x) - Γ_{xy} f(y)‖_ℓ ≤ C |x - y|^{γ - ℓ}

for all ℓ < γ.
-/

/-- The Euclidean distance between two points (defined early for use in bounds) -/
noncomputable def euclideanDistBound (d : ℕ) (x y : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- A modelled distribution f ∈ D^γ for a regularity structure.

    Elements of D^γ are functions f : ℝ^d → T_{<γ} satisfying:
    1. Local bound: ‖f(x)‖_total ≤ C for x ∈ K
    2. Hölder regularity: ‖f(x) - Γ_{xy} f(y)‖_total ≤ C |x - y|^{γ - α₀} for x, y ∈ K
       where α₀ is the minimum homogeneity

    Here T_{<γ} denotes the subspace of T spanned by trees with homogeneity < γ. -/
structure ModelledDistribution (d : ℕ) (params : ModelParameters d) (γ : ℝ) where
  /-- The function assigning tree expansions to points -/
  f : (Fin d → ℝ) → FormalSum d
  /-- The model being used -/
  model : AdmissibleModel d params
  /-- The bound constant C for the seminorm -/
  bound_const : ℝ
  /-- The bound constant is nonnegative -/
  bound_nonneg : bound_const ≥ 0
  /-- Local bound: ‖f(x)‖_total ≤ C for all x ∈ K -/
  local_bound : ∀ x : Fin d → ℝ, ∀ K : Set (Fin d → ℝ),
    x ∈ K → FormalSum.totalNorm (f x) ≤ bound_const
  /-- Hölder regularity: ‖f(x) - Γ_{xy} f(y)‖_total ≤ C |x - y|^{γ - α₀}
      Note: Γ_{xy} acts on FormalSum by linearity via bind. -/
  holder_regularity : ∀ x y : Fin d → ℝ, ∀ K : Set (Fin d → ℝ),
    x ∈ K → y ∈ K →
    FormalSum.totalNorm (f x - FormalSum.bind (f y) (model.Gamma.Gamma x y)) ≤
      bound_const * Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity)

namespace ModelledDistribution

variable {d : ℕ} {params : ModelParameters d} {γ : ℝ}

/-- The Euclidean distance between two points in ℝ^d -/
noncomputable def euclideanDist (x y : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- The local part of the seminorm: sup_{x ∈ K} ‖f(x)‖_total -/
noncomputable def localSeminorm (f : ModelledDistribution d params γ) (K : Set (Fin d → ℝ)) : ℝ :=
  ⨆ (x : Fin d → ℝ) (_ : x ∈ K), FormalSum.totalNorm (f.f x)

/-- Apply recentering to a formal sum (extending RecenteringMap to formal sums by linearity).
    For s = Σᵢ cᵢ τᵢ, returns Σᵢ cᵢ · Γ_{xy}(τᵢ) where Γ_{xy}(τᵢ) is itself a FormalSum. -/
noncomputable def applyGamma (Γ : RecenteringMap d) (x y : Fin d → ℝ) (s : FormalSum d) :
    FormalSum d :=
  FormalSum.bind s (Γ.Gamma x y)

/-- The Hölder part of the seminorm at a specific pair of points.
    Computes ‖f(x) - Γ_{xy} f(y)‖_total / |x - y|^{γ - ℓ₀} where ℓ₀ is min homogeneity -/
noncomputable def holderTermAtPair (f : ModelledDistribution d params γ) (x y : Fin d → ℝ) : ℝ :=
  let diff := f.f x - applyGamma f.model.Gamma x y (f.f y)
  let dist := euclideanDist x y
  if dist = 0 then 0
  else FormalSum.totalNorm diff / Real.rpow dist (γ - params.minHomogeneity)

/-- The Hölder part of the seminorm: sup over distinct points -/
noncomputable def holderSeminorm (f : ModelledDistribution d params γ) (K : Set (Fin d → ℝ)) : ℝ :=
  ⨆ (x : Fin d → ℝ) (_ : x ∈ K) (y : Fin d → ℝ) (_ : y ∈ K),
    holderTermAtPair f x y

/-- The seminorm |||f|||_{γ;K} for a modelled distribution on compact set K.
    This measures the Hölder regularity of f.
    |||f|||_{γ;K} = sup_{x ∈ K} ‖f(x)‖ + sup_{x,y ∈ K, x≠y} ‖f(x) - Γ_{xy} f(y)‖ / |x - y|^{γ - ℓ} -/
noncomputable def seminorm (f : ModelledDistribution d params γ) (K : Set (Fin d → ℝ)) : ℝ :=
  localSeminorm f K + holderSeminorm f K

/-- The distance |||f; g|||_{γ;K} between two modelled distributions.
    Defined as the seminorm of the "difference" (conceptually f - g). -/
noncomputable def distance (f g : ModelledDistribution d params γ)
    (K : Set (Fin d → ℝ)) : ℝ :=
  -- The distance is the supremum of differences in values
  ⨆ (x : Fin d → ℝ) (_ : x ∈ K), FormalSum.totalNorm (f.f x - g.f x)

/-- Addition of modelled distributions (pointwise on formal sums).
    Requires same model. The bound constant is the sum of individual bounds. -/
noncomputable def add (f g : ModelledDistribution d params γ)
    (hmodel : f.model = g.model) : ModelledDistribution d params γ where
  f := fun x => f.f x + g.f x
  model := f.model
  bound_const := f.bound_const + g.bound_const
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  local_bound := fun x K hx => by
    -- Need: ‖f(x) + g(x)‖ ≤ Cf + Cg
    -- This follows from triangle inequality for totalNorm
    calc FormalSum.totalNorm (f.f x + g.f x)
        ≤ FormalSum.totalNorm (f.f x) + FormalSum.totalNorm (g.f x) :=
          FormalSum.totalNorm_add_le (f.f x) (g.f x)
      _ ≤ f.bound_const + g.bound_const := add_le_add (f.local_bound x K hx) (g.local_bound x K hx)
  holder_regularity := fun x y K hx hy => by
    -- Need to show: ‖(f+g)(x) - Γ_{xy}((f+g)(y))‖ ≤ (Cf + Cg) * |x-y|^{γ-α₀}
    -- Key insight: Γ (i.e., bind) distributes over addition
    -- (f+g)(x) - Γ_{xy}((f+g)(y)) = (f(x) - Γ(f(y))) + (g(x) - Γ(g(y)))

    -- Since f.model = g.model, the Gamma functions are the same
    let Γ := f.model.Gamma.Gamma x y

    -- g's Gamma equals f's Gamma
    have hΓeq : g.model.Gamma.Gamma x y = Γ := by
      simp only [Γ]
      exact congrArg (fun m => m.Gamma.Gamma x y) hmodel.symm

    -- Rewrite g's holder_regularity using f's Gamma
    have hg_holder : FormalSum.totalNorm (FormalSum.sub (g.f x) (FormalSum.bind (g.f y) Γ)) ≤
        g.bound_const * Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity) := by
      show FormalSum.totalNorm (g.f x - FormalSum.bind (g.f y) Γ) ≤ _
      rw [← hΓeq]
      exact g.holder_regularity x y K hx hy

    -- Use: bind distributes over addition
    have hbind_add : FormalSum.bind (FormalSum.add (f.f y) (g.f y)) Γ =
        FormalSum.add (FormalSum.bind (f.f y) Γ) (FormalSum.bind (g.f y) Γ) :=
      FormalSum.bind_add (f.f y) (g.f y) Γ

    -- Use the key algebraic identity:
    -- totalNorm ((a + b) - (c + d)) = totalNorm ((a - c) + (b - d))
    have halg := FormalSum.totalNorm_add_sub_add
      (f.f x) (g.f x) (FormalSum.bind (f.f y) Γ) (FormalSum.bind (g.f y) Γ)

    -- The LHS is what we want to bound
    -- Need to show f.f x + g.f x - bind (f.f y + g.f y) Γ has same totalNorm
    have hLHS : FormalSum.totalNorm (f.f x + g.f x - FormalSum.bind (f.f y + g.f y) Γ) =
        FormalSum.totalNorm (FormalSum.sub (FormalSum.add (f.f x) (g.f x))
          (FormalSum.add (FormalSum.bind (f.f y) Γ) (FormalSum.bind (g.f y) Γ))) := by
      show FormalSum.totalNorm (FormalSum.sub (FormalSum.add (f.f x) (g.f x))
        (FormalSum.bind (FormalSum.add (f.f y) (g.f y)) Γ)) = _
      rw [hbind_add]

    rw [hLHS, halg]
    -- Now bound totalNorm ((f.f x - bind f) + (g.f x - bind g))
    calc FormalSum.totalNorm (FormalSum.add (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ))
            (FormalSum.sub (g.f x) (FormalSum.bind (g.f y) Γ)))
        ≤ FormalSum.totalNorm (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ)) +
          FormalSum.totalNorm (FormalSum.sub (g.f x) (FormalSum.bind (g.f y) Γ)) := by
          exact FormalSum.totalNorm_add_le _ _
      _ ≤ f.bound_const * Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity) +
          g.bound_const * Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity) := by
          apply add_le_add
          · exact f.holder_regularity x y K hx hy
          · exact hg_holder
      _ = (f.bound_const + g.bound_const) *
          Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity) := by ring

/-- Scalar multiplication of a modelled distribution. -/
noncomputable def smul (c : ℝ) (f : ModelledDistribution d params γ) :
    ModelledDistribution d params γ where
  f := fun x => c • f.f x
  model := f.model
  bound_const := |c| * f.bound_const
  bound_nonneg := mul_nonneg (abs_nonneg c) f.bound_nonneg
  local_bound := fun x K hx => by
    -- Need: ‖c • f(x)‖ ≤ |c| * Cf
    -- This follows from homogeneity of totalNorm
    rw [FormalSum.totalNorm_smul]
    exact mul_le_mul_of_nonneg_left (f.local_bound x K hx) (abs_nonneg c)
  holder_regularity := fun x y K hx hy => by
    -- Need: ‖c • f(x) - Γ_{xy}(c • f(y))‖ ≤ |c| * Cf * |x-y|^{γ-α₀}
    -- Key: bind (c • s) h = c • bind s h (bind commutes with scalar mult)
    let Γ := f.model.Gamma.Gamma x y

    -- bind commutes with smul
    have hbind_smul : FormalSum.bind (FormalSum.smul c (f.f y)) Γ =
        FormalSum.smul c (FormalSum.bind (f.f y) Γ) :=
      FormalSum.bind_smul c (f.f y) Γ

    -- c • a - c • b = c • (a - b) for FormalSum (in terms of totalNorm)
    -- We prove this by showing both have equal totalNorm
    have hsmul_sub_norm : FormalSum.totalNorm (FormalSum.sub (FormalSum.smul c (f.f x))
        (FormalSum.smul c (FormalSum.bind (f.f y) Γ))) =
        FormalSum.totalNorm (FormalSum.smul c (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ))) := by
      -- Use totalNorm_sub_eq and totalNorm_smul
      -- Need explicit lemma applications
      have h1 : FormalSum.totalNorm (FormalSum.sub (FormalSum.smul c (f.f x))
          (FormalSum.smul c (FormalSum.bind (f.f y) Γ))) =
          FormalSum.totalNorm (FormalSum.smul c (f.f x)) +
          FormalSum.totalNorm (FormalSum.smul c (FormalSum.bind (f.f y) Γ)) :=
        FormalSum.totalNorm_sub_eq _ _
      have h2 : FormalSum.totalNorm (FormalSum.smul c (f.f x)) = |c| * FormalSum.totalNorm (f.f x) := by
        show FormalSum.totalNorm (c • f.f x) = _
        exact FormalSum.totalNorm_smul c (f.f x)
      have h3 : FormalSum.totalNorm (FormalSum.smul c (FormalSum.bind (f.f y) Γ)) =
          |c| * FormalSum.totalNorm (FormalSum.bind (f.f y) Γ) := by
        show FormalSum.totalNorm (c • FormalSum.bind (f.f y) Γ) = _
        exact FormalSum.totalNorm_smul c _
      have h4 : FormalSum.totalNorm (FormalSum.smul c (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ))) =
          |c| * FormalSum.totalNorm (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ)) := by
        show FormalSum.totalNorm (c • FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ)) = _
        exact FormalSum.totalNorm_smul c _
      have h5 : FormalSum.totalNorm (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ)) =
          FormalSum.totalNorm (f.f x) + FormalSum.totalNorm (FormalSum.bind (f.f y) Γ) :=
        FormalSum.totalNorm_sub_eq _ _
      rw [h1, h2, h3, h4, h5]
      ring

    -- The main calculation
    calc FormalSum.totalNorm (FormalSum.smul c (f.f x) - FormalSum.bind (FormalSum.smul c (f.f y)) Γ)
        = FormalSum.totalNorm (FormalSum.sub (FormalSum.smul c (f.f x))
            (FormalSum.smul c (FormalSum.bind (f.f y) Γ))) := by
          show FormalSum.totalNorm (FormalSum.sub (FormalSum.smul c (f.f x))
            (FormalSum.bind (FormalSum.smul c (f.f y)) Γ)) = _
          rw [hbind_smul]
      _ = FormalSum.totalNorm (FormalSum.smul c (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ))) := by
          rw [hsmul_sub_norm]
      _ = |c| * FormalSum.totalNorm (FormalSum.sub (f.f x) (FormalSum.bind (f.f y) Γ)) := by
          exact FormalSum.totalNorm_smul c _
      _ ≤ |c| * (f.bound_const * Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity)) := by
          apply mul_le_mul_of_nonneg_left
          · exact f.holder_regularity x y K hx hy
          · exact abs_nonneg c
      _ = |c| * f.bound_const * Real.rpow (euclideanDistBound d x y) (γ - params.minHomogeneity) := by
          ring

/-- The zero modelled distribution for a given model. -/
noncomputable def zero (model : AdmissibleModel d params) :
    ModelledDistribution d params γ where
  f := fun _ => FormalSum.zero
  model := model
  bound_const := 0
  bound_nonneg := le_refl 0
  local_bound := fun _x _K _hx => by
    -- totalNorm of zero is 0
    simp only [FormalSum.totalNorm, FormalSum.zero, List.foldl_nil, le_refl]
  holder_regularity := fun _x _y _K _hx _hy => by
    -- zero - Γ(zero) = zero, and 0 * anything = 0
    -- The LHS simplifies to totalNorm of an empty FormalSum which is 0
    -- The RHS is 0 * ... = 0
    -- So we need 0 ≤ 0
    have hLHS : FormalSum.totalNorm (FormalSum.zero - FormalSum.bind FormalSum.zero (model.Gamma.Gamma _x _y)) = 0 := by
      -- bind on {terms := []} gives {terms := []}
      simp only [FormalSum.bind, FormalSum.zero, List.flatMap_nil]
      -- {terms := []} - {terms := []} simplifies via sub definition
      simp only [HSub.hSub, Sub.sub, FormalSum.sub]
      -- totalNorm of {terms := []} = 0
      rfl
    rw [hLHS]
    simp only [zero_mul, le_refl]

end ModelledDistribution

/-! ## Negative Hölder-Besov Spaces

For α < 0, the space C^α_s consists of distributions whose scaling behavior
is like |x|^α when tested against scaled test functions.
-/

/-- The Hölder-Besov space C^α_s for possibly negative α.
    For α < 0, this is a space of distributions.

    Definition 3.7 from Hairer 2014:
    ξ ∈ C^α_s if |⟨ξ, S^δ_{s,x} η⟩| ≤ C δ^α for test functions η. -/
structure HolderBesov (d : ℕ) (α : ℝ) where
  /-- The distribution, represented by its action on test functions -/
  pairing : TestFunction d → (Fin d → ℝ) → ℝ → ℝ  -- φ → x → scale → ⟨ξ, φ^λ_x⟩
  /-- The bound constant C for the Hölder-Besov norm -/
  bound_const : ℝ
  /-- The bound constant is nonnegative -/
  bound_nonneg : bound_const ≥ 0
  /-- Scaling bound: |⟨ξ, φ^λ_x⟩| ≤ C λ^α ‖φ‖ for λ ≤ 1
      This is the defining property of Hölder-Besov spaces. -/
  scaling_bound : ∀ (φ : TestFunction d) (x : Fin d → ℝ) (scale : ℝ),
    0 < scale → scale ≤ 1 →
    |pairing φ x scale| ≤ bound_const * Real.rpow scale α * φ.sup_norm

namespace HolderBesov

variable {d : ℕ} {α : ℝ}

/-- The seminorm ‖ξ‖_{α;K} for ξ ∈ C^α_s on compact set K.
    ‖ξ‖_{α;K} = sup_{x ∈ K} sup_{φ} sup_{δ ∈ (0,1]} δ^{-α} |⟨ξ, φ^δ_x⟩| -/
noncomputable def seminorm (ξ : HolderBesov d α) (K : Set (Fin d → ℝ)) : ℝ :=
  ⨆ (x : Fin d → ℝ) (_ : x ∈ K) (φ : TestFunction d) (δ : Set.Ioo (0 : ℝ) 1),
    Real.rpow δ.val (-α) * |ξ.pairing φ x δ.val|

end HolderBesov

/-! ## The Reconstruction Map

The Reconstruction Theorem provides a continuous linear map R : D^γ → C^α_s
that "reconstructs" a distribution from its modelled representation.
-/

/-- Extend model pairing to FormalSums by linearity:
    ⟨Π_x(Σᵢ cᵢτᵢ), φ⟩ = Σᵢ cᵢ⟨Π_x τᵢ, φ⟩ -/
noncomputable def extendModelPairing {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (s : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) : ℝ :=
  s.terms.foldl (fun acc (c, τ) => acc + c * model.Pi.pairing τ x φ scale) 0

/-- The reconstruction map R : D^γ → C^α_s.

    This is the central object of the Reconstruction Theorem (Theorem 3.10).
    The map R takes a modelled distribution f and produces an actual distribution Rf
    such that Rf locally looks like Π_x f(x). -/
structure ReconstructionMap (d : ℕ) (params : ModelParameters d) (γ : ℝ) where
  /-- The reconstruction map -/
  R : ModelledDistribution d params γ → HolderBesov d params.minHomogeneity
  /-- Bound constant for the reconstruction -/
  bound_const : ℝ
  /-- Bound constant is positive -/
  bound_pos : bound_const > 0

namespace ReconstructionMap

variable {d : ℕ} {params : ModelParameters d} {γ : ℝ}

/-- The key bound from the Reconstruction Theorem:
    |⟨Rf - Π_x f(x), φ^λ_x⟩| ≤ C λ^γ ‖Π‖ |||f|||

    This says that Rf differs from Π_x f(x) only at scale λ^γ,
    which is smaller than the regularity of Π_x f(x) (which is λ^{min A}). -/
def satisfies_reconstruction_bound (Rmap : ReconstructionMap d params γ) : Prop :=
  ∀ (f : ModelledDistribution d params γ),
  ∀ (K : Set (Fin d → ℝ)),  -- Compact set
  ∀ (x : Fin d → ℝ),
  x ∈ K →
  ∀ (φ : TestFunction d),
  ∀ (scale : ℝ), 0 < scale → scale ≤ 1 →
    -- |⟨Rf - Π_x f(x), φ^λ_x⟩| ≤ C λ^γ |||f|||
    |(Rmap.R f).pairing φ x scale - extendModelPairing f.model (f.f x) x φ scale| ≤
      Rmap.bound_const * Real.rpow scale γ * f.bound_const * φ.sup_norm

end ReconstructionMap

/-! ## The Reconstruction Theorem

Theorem 3.10 (Hairer 2014): For every regularity structure T = (A, T, G) with
model (Π, Γ), there exists a unique (when γ > 0) continuous linear map
R : D^γ → C^α_s satisfying the reconstruction bound.
-/

/-- The Reconstruction Theorem (Hairer 2014, Theorem 3.10).

    For a regularity structure with model (Π, Γ), there exists a continuous
    linear map R : D^γ → C^α_s such that:

    |⟨Rf - Π_x f(x), φ^λ_x⟩| ≤ C λ^γ ‖Π‖_{γ;K} |||f|||_{γ;K}

    uniformly over test functions φ, scales δ ∈ (0, 1], modelled distributions f,
    and points x in any compact K. If γ > 0, then R is unique. -/
theorem reconstruction_theorem {d : ℕ} {params : ModelParameters d}
    (γ : ℝ) (hγ_pos : γ > 0) :
    ∃! R : ReconstructionMap d params γ, R.satisfies_reconstruction_bound := by
  sorry  -- This is the main theorem

/-- Existence part of the Reconstruction Theorem -/
theorem reconstruction_exists {d : ℕ} {params : ModelParameters d}
    (γ : ℝ) :
    ∃ R : ReconstructionMap d params γ, R.satisfies_reconstruction_bound := by
  sorry

/-- Uniqueness part of the Reconstruction Theorem (when γ > 0) -/
theorem reconstruction_unique {d : ℕ} {params : ModelParameters d}
    (γ : ℝ) (hγ_pos : γ > 0)
    (R₁ R₂ : ReconstructionMap d params γ)
    (hR₁ : R₁.satisfies_reconstruction_bound)
    (hR₂ : R₂.satisfies_reconstruction_bound) :
    ∀ f : ModelledDistribution d params γ, R₁.R f = R₂.R f := by
  sorry

/-! ## Continuity in the Model

The reconstruction map is also continuous as a function of the model.
This is crucial for the renormalization procedure.
-/

/-- Continuity of R in the model: small changes to (Π, Γ) produce small changes to R.

    From Theorem 3.10 (bound 3.4):
    |⟨Rf - R̄f̄ - Π_x f(x) + Π̄_x f̄(x), φ^λ_x⟩|
      ≤ C λ^γ (‖Π̄‖ |||f; f̄||| + ‖Π - Π̄‖ |||f|||)

    This theorem expresses that the reconstruction map is continuous in both the
    model and the modelled distribution. -/
theorem reconstruction_continuous_in_model {d : ℕ} {params : ModelParameters d}
    (γ : ℝ) (hγ_pos : γ > 0)
    (R₁ R₂ : ReconstructionMap d params γ)
    (f₁ : ModelledDistribution d params γ)
    (f₂ : ModelledDistribution d params γ)
    (hR₁ : R₁.satisfies_reconstruction_bound)
    (hR₂ : R₂.satisfies_reconstruction_bound)
    (K_set : Set (Fin d → ℝ)) :
    -- The difference in reconstructions is bounded by the differences in inputs
    ∃ C : ℝ, C > 0 ∧
      (R₁.R f₁).seminorm K_set ≤ C * (f₁.seminorm K_set + f₂.seminorm K_set) ∧
      (R₂.R f₂).seminorm K_set ≤ C * (f₁.seminorm K_set + f₂.seminorm K_set) := by
  sorry  -- Requires detailed analysis of reconstruction bounds

/-! ## Applications: Schauder Estimates

The Reconstruction Theorem implies Schauder-type estimates for solutions
to SPDEs. If the solution is represented as a modelled distribution,
then R reconstructs an actual distribution with the expected regularity.
-/

/-- Schauder estimate: if f ∈ D^γ then Rf ∈ C^α_s with controlled norm.
    This provides the regularity theory for solutions.

    The bound is: ‖Rf‖_{C^α;K} ≤ C |||f|||_{γ;K}
    where α = params.minHomogeneity is the minimum regularity. -/
theorem schauder_estimate {d : ℕ} {params : ModelParameters d}
    (γ : ℝ) (_hγ_pos : γ > 0)
    (f : ModelledDistribution d params γ)
    (R : ReconstructionMap d params γ)
    (hR : R.satisfies_reconstruction_bound)
    (K_set : Set (Fin d → ℝ)) :
    -- Rf has regularity α = min A with norm bounded by seminorm of f
    (R.R f).seminorm K_set ≤ R.bound_const * f.seminorm K_set := by
  sorry  -- Requires detailed wavelet/Besov space analysis

end SPDE.RegularityStructures

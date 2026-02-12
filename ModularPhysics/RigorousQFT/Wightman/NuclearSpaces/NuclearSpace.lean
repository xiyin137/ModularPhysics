/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Algebra.Module.LocallyConvex
import ModularPhysics.RigorousQFT.Wightman.NuclearSpaces.NuclearOperator

/-!
# Nuclear Spaces

This file defines nuclear spaces using Grothendieck/Pietsch characterization.

## Main Definitions

* `NuclearSpace` - A locally convex space E is nuclear if for every continuous seminorm p,
  there exists a continuous seminorm q ≥ p such that p is "nuclearly dominated" by q.
* `NuclearFrechet` - A nuclear Fréchet space presented via seminorms with nuclear steps.

## Mathematical Background

A locally convex topological vector space E is **nuclear** (Grothendieck) if its topology
is defined by a family of seminorms {p_α} such that for every p_α, there exists p_β ≥ p_α
with the canonical map from the completion of E/ker(p_β) to E/ker(p_α) being a nuclear
operator.

Equivalent characterizations:
1. (Grothendieck) Via nuclear maps between seminorm completions
2. (Pietsch) For every continuous seminorm p, there exist fₙ ∈ E* and cₙ ≥ 0 with
   Σ cₙ < ∞ such that p(x) ≤ Σ |fₙ(x)| · cₙ and each fₙ continuous
3. (Schwartz) Projective limit of Hilbert spaces with Hilbert-Schmidt connecting maps

Key examples: S(ℝⁿ), C^∞(M), distributions, finite-dimensional spaces.
Non-examples: infinite-dimensional Banach spaces.

## References

* Grothendieck, "Produits tensoriels topologiques et espaces nucléaires" (1955)
* Pietsch, "Nuclear Locally Convex Spaces" (1972)
* Trèves, "Topological Vector Spaces, Distributions and Kernels" (1967), Ch. 50
-/

noncomputable section

open scoped NNReal Topology
open Filter

/-! ### Nuclear Space Definition (Pietsch characterization) -/

/-- A locally convex topological vector space over ℝ is **nuclear** if for every continuous
    seminorm p, there exist continuous linear functionals (fₙ : E →L[ℝ] ℝ) and non-negative
    reals (cₙ) with Σ cₙ < ∞, and a continuous seminorm q ≥ p, such that:
    (1) p(x) ≤ Σₙ |fₙ(x)| · cₙ for all x
    (2) |fₙ(x)| ≤ q(x) for all x, n

    This is Pietsch's characterization, equivalent to Grothendieck's definition that
    the canonical map E_q → E_p between seminorm completions is nuclear.

    We follow the `LocallyConvexSpace` pattern in Mathlib for the type class binders. -/
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop where
  nuclear_dominance : ∀ (p : Seminorm ℝ E), Continuous p →
    ∃ (q : Seminorm ℝ E), Continuous q ∧ (∀ x, p x ≤ q x) ∧
    ∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧
      Summable c ∧
      (∀ n x, ‖f n x‖ ≤ q x) ∧
      (∀ x, p x ≤ ∑' n, ‖f n x‖ * c n)

/-! ### Basic Properties of Nuclear Spaces -/

namespace NuclearSpace

/-- Finite-dimensional spaces are nuclear. -/
theorem finiteDimensional (V : Type*) [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [FiniteDimensional ℝ V] [T2Space V] : NuclearSpace V where
  nuclear_dominance := by
    intro p hp
    sorry

/-- A closed subspace of a nuclear space is nuclear. -/
theorem subspace_nuclear (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E]
    [NuclearSpace E] (S : Submodule ℝ E) (_hclosed : IsClosed (S : Set E)) :
    NuclearSpace S := by
  sorry

/-- Countable products of nuclear spaces are nuclear. -/
theorem product_nuclear (ι : Type*) [Countable ι]
    (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)]
    [∀ i, NuclearSpace (E i)] : NuclearSpace (∀ i, E i) := by
  sorry

end NuclearSpace

/-! ### Nuclear Fréchet Space Presentation -/

/-- A nuclear Fréchet space presented as a sequence of seminorms with nuclear steps.
    This is the most practical formulation for QFT applications.

    The space E comes equipped with a countable family of seminorms (pₙ)
    that define its topology, and for each n the "identity" from (E, pₙ₊₁)
    to (E, pₙ) admits a nuclear factorization: there exist linear functionals φₖ
    bounded by pₙ₊₁ and summable coefficients cₖ with pₙ(x) ≤ Σₖ |φₖ(x)| · cₖ.

    For Schwartz space, the pₙ are the Schwartz seminorms involving
    polynomial weights and derivatives. -/
structure NuclearFrechet where
  /-- The underlying space -/
  Space : Type*
  /-- Additive group structure -/
  instAddCommGroup : AddCommGroup Space
  /-- ℝ-module structure -/
  instModule : Module ℝ Space
  /-- Topology -/
  instTopologicalSpace : TopologicalSpace Space
  /-- The defining family of seminorms (indexed by ℕ) -/
  seminorms : ℕ → Seminorm ℝ Space
  /-- Seminorms are increasing: pₙ ≤ pₙ₊₁ -/
  seminorms_mono : ∀ n x, seminorms n x ≤ seminorms (n + 1) x
  /-- The seminorms separate points (Hausdorff condition) -/
  separating : ∀ x, (∀ n, seminorms n x = 0) → x = 0
  /-- Each defining seminorm is continuous with respect to the topology -/
  continuous_seminorms : ∀ n,
    @Continuous Space ℝ instTopologicalSpace inferInstance (seminorms n)
  /-- Every continuous seminorm on the space is bounded by some defining seminorm
      (the defining seminorms generate the topology). -/
  seminorms_generating : ∀ (p : Seminorm ℝ Space),
    @Continuous Space ℝ instTopologicalSpace inferInstance p →
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ x, p x ≤ C * seminorms n x
  /-- Nuclear condition: for each n, pₙ is nuclearly dominated by pₙ₊₁.
      There exist linear functionals bounded by pₙ₊₁ and summable coefficients
      that provide a nuclear-type bound on pₙ.

      Note: The functionals are given as linear maps, but they are automatically
      continuous because they are bounded by the continuous seminorm pₙ₊₁. -/
  nuclear_step : ∀ (n : ℕ),
    ∃ (φ : ℕ → Space →ₗ[ℝ] ℝ) (c : ℕ → ℝ),
      (∀ k, 0 ≤ c k) ∧
      Summable c ∧
      (∀ k x, |φ k x| ≤ seminorms (n + 1) x) ∧
      (∀ x, seminorms n x ≤ ∑' k, |φ k x| * c k)

/-! ### Connection to NuclearSpace class -/

/-- A nuclear Fréchet presentation gives rise to a NuclearSpace instance.

    The key step is that any continuous seminorm p on E is bounded by some
    finite linear combination of the defining seminorms pₙ (by definition of
    the topology), and then the nuclear_step condition propagates. -/
theorem NuclearFrechet.toNuclearSpace (NF : NuclearFrechet) :
    @NuclearSpace NF.Space NF.instAddCommGroup NF.instModule NF.instTopologicalSpace := by
  letI := NF.instAddCommGroup
  letI := NF.instModule
  letI := NF.instTopologicalSpace
  constructor
  intro p hp
  sorry

end

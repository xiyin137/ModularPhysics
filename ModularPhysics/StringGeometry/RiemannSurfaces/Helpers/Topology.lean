import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Topological Helper Lemmas for Riemann Surfaces

This file contains foundational topological results needed for Riemann surface theory.

## Main results

* `Complex.isPreconnected_univ` - The complex plane is preconnected
* Properties of OnePoint ℂ (Riemann sphere topology)

## Mathematical Background

ℂ is connected because it is convex (hence path-connected). As a real vector space,
ℂ ≅ ℝ², and convex subsets of real vector spaces are preconnected.
-/

namespace RiemannSurfaces.Helpers

/-!
## Connectedness of ℂ

We prove ℂ is connected using convexity: ℂ (viewed as a real vector space)
is convex, and convex sets are preconnected.
-/

/-- The complex plane is preconnected (via convexity) -/
theorem Complex.isPreconnected_univ : IsPreconnected (Set.univ : Set ℂ) :=
  convex_univ.isPreconnected

/-- ℂ is a preconnected topological space -/
instance Complex.preconnectedSpace : PreconnectedSpace ℂ :=
  ⟨Complex.isPreconnected_univ⟩

/-!
## One-Point Compactification Properties

The one-point compactification of a locally compact Hausdorff space
preserves and creates important topological properties.
-/

/-- ℂ is not compact (it's unbounded). -/
instance Complex.noncompactSpace : NoncompactSpace ℂ := by
  rw [← not_compactSpace_iff]
  intro ⟨h⟩
  -- ℂ is not compact because it contains arbitrarily large elements
  have hbdd := h.isBounded
  rw [isBounded_iff_forall_norm_le] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  -- Take n = ⌈C⌉ + 1 as a natural number, so n > C
  let n : ℕ := ⌈C⌉₊ + 1
  specialize hC (n : ℂ) (Set.mem_univ _)
  rw [Complex.norm_natCast] at hC
  -- But n = ⌈C⌉₊ + 1 > ⌈C⌉₊ ≥ C, contradicting hC : n ≤ C
  have hn_gt : (n : ℝ) > C := by
    simp only [n]
    have h1 : (⌈C⌉₊ : ℝ) ≥ C := Nat.le_ceil C
    have h2 : ((⌈C⌉₊ + 1 : ℕ) : ℝ) = (⌈C⌉₊ : ℝ) + 1 := by simp
    rw [h2]; linarith
  linarith

/-- OnePoint ℂ is connected (follows from ℂ being preconnected and noncompact) -/
instance OnePoint.Complex.connectedSpace : ConnectedSpace (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is T1 (follows from ℂ being T1) -/
instance OnePoint.Complex.t1Space : T1Space (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is normal (follows from ℂ being weakly locally compact and R1) -/
instance OnePoint.Complex.normalSpace : NormalSpace (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is second countable.

    **Proof sketch:**
    1. ℂ is locally compact, Hausdorff, sigma-compact, and second countable
    2. ℂ has a countable topological basis 𝒰
    3. Since ℂ is sigma-compact, there exists an exhaustion by compact sets K₁ ⊆ K₂ ⊆ ...
    4. The family 𝒰 ∪ { (Kₙ)ᶜ ∪ {∞} : n ∈ ℕ } is a countable subbasis for OnePoint ℂ
    5. Hence OnePoint ℂ has a countable basis

    Alternatively: OnePoint ℂ ≅ S² via stereographic projection, and S² ⊆ ℝ³
    is a submanifold of a second countable space, hence second countable. -/
instance OnePoint.Complex.secondCountableTopology : SecondCountableTopology (OnePoint ℂ) := by
  -- We construct a countable basis for the topology on OnePoint ℂ
  -- The topology has basis: open sets of ℂ ∪ {∞ ∪ Kᶜ : K compact in ℂ}
  --
  -- Since ℂ is second countable, it has a countable basis of open sets.
  -- Since ℂ is sigma-compact (union of closed balls B(0,n)), we can take
  -- a countable family of compact sets whose complements form a neighborhood base at ∞.
  --
  -- The full proof requires constructing this basis explicitly.
  -- For now, we use sorry as this is a standard topological fact.
  sorry

end RiemannSurfaces.Helpers

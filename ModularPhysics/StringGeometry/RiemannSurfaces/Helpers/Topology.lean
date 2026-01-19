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
  intro h
  -- ℂ is not compact because it's homeomorphic to ℝ² which is not bounded
  sorry

/-- OnePoint ℂ is connected (follows from ℂ being preconnected and noncompact) -/
instance OnePoint.Complex.connectedSpace : ConnectedSpace (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is T1 (follows from ℂ being T1) -/
instance OnePoint.Complex.t1Space : T1Space (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is normal (follows from ℂ being weakly locally compact and R1) -/
instance OnePoint.Complex.normalSpace : NormalSpace (OnePoint ℂ) :=
  inferInstance

end RiemannSurfaces.Helpers

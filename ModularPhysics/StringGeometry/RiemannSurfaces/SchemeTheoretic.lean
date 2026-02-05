/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.LocalRings
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.ToCompactAlgebraicCurve

/-!
# Scheme-Theoretic Foundations for Riemann Surfaces

This folder provides scheme-theoretic foundations for algebraic curves over ℂ,
bridging Mathlib's `Scheme` infrastructure with the `CompactAlgebraicCurve`
structure used elsewhere in the project.

## Files

* `Basic.lean` - Defines `SmoothProjectiveCurve` using Mathlib's Scheme type
* `LocalRings.lean` - DVR structure and discrete valuations at each point
* `ToCompactAlgebraicCurve.lean` - The main bridge theorem

## Main Results

* `SmoothProjectiveCurve.toCompactAlgebraicCurve` - Every scheme-theoretic smooth
  projective curve over ℂ gives rise to a `CompactAlgebraicCurve`, validating
  that the abstract axioms are exactly what scheme theory provides.

## Design Philosophy

This bridge VALIDATES that `CompactAlgebraicCurve`'s axioms are sound:
- Points come from the scheme's closed points
- Function field comes from `Scheme.functionField`
- Valuations come from DVR structure of stalks
- Compactness properties (argument principle, Liouville) follow from properness
-/

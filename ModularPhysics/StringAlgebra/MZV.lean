/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringAlgebra.MZV.Basic
import ModularPhysics.StringAlgebra.MZV.IteratedIntegral
import ModularPhysics.StringAlgebra.MZV.ShuffleAlgebra
import ModularPhysics.StringAlgebra.MZV.StuffleAlgebra
import ModularPhysics.StringAlgebra.MZV.DoubleShuffle
import ModularPhysics.StringAlgebra.MZV.Relations
import ModularPhysics.StringAlgebra.MZV.Motivic
import ModularPhysics.StringAlgebra.MZV.Polylogarithm
import ModularPhysics.StringAlgebra.MZV.Associator

/-!
# Multiple Zeta Values

This module provides the algebraic theory of multiple zeta values (MZVs)
following the framework of Francis Brown.

## Contents

* `Basic` - Compositions, weight, depth, admissibility
* `IteratedIntegral` - MZVs as iterated integrals on P¹ \ {0,1,∞}
* `ShuffleAlgebra` - The shuffle product on words
* `StuffleAlgebra` - The stuffle (quasi-shuffle) product on compositions
* `DoubleShuffle` - Double shuffle relations and regularization
* `Relations` - Explicit MZV relations (sum formula, duality, Ohno)
* `Motivic` - Motivic MZVs and the period map
* `Polylogarithm` - Multiple polylogarithms
* `Associator` - The Drinfeld associator

## Mathematical Background

Multiple zeta values are defined for admissible compositions (s₁,...,sₖ):

  ζ(s₁,...,sₖ) = Σ_{n₁ > ... > nₖ ≥ 1} 1/(n₁^{s₁} ⋯ nₖ^{sₖ})

They satisfy two product structures:
- **Shuffle product**: from iterated integral representation
- **Stuffle product**: from series representation

The compatibility of these products gives the double shuffle relations.

## References

* Brown - "Mixed Tate motives over ℤ"
* Hoffman - "Multiple harmonic series"
* Zagier - "Values of zeta functions and their applications"
-/

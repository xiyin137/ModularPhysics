/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.HyperfiniteRandomWalk
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.LoebMeasure
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.QuadraticVariation

/-!
# Nonstandard Analysis Approach to Stochastic Processes

This module develops stochastic processes (particularly Brownian motion) using
nonstandard analysis / hyperreal methods.

## Overview

The classical construction of Brownian motion requires substantial measure-theoretic
machinery:
- Kolmogorov extension theorem
- Construction of Wiener measure
- Careful handling of null sets and path regularity

The nonstandard approach (Anderson 1976, Loeb 1975) is conceptually simpler:

1. **Hyperfinite random walk**: Take N coin flips where N is an infinite hypernatural.
   The walk has infinitesimal time steps dt = T/N and space steps dx = √dt.

2. **Internal probability**: On the hyperfinite sample space {-1,+1}^N, probability
   is just counting: P(A) = |A|/2^N. This is finitely additive.

3. **Loeb measure**: Taking standard parts of internal probabilities and extending
   via Carathéodory gives a σ-additive measure - the Loeb measure.

4. **Standard part of paths**: Taking standard parts of hyperfinite walk paths
   gives continuous functions. The Loeb measure pushes forward to Wiener measure.

## Contents

* `HyperfiniteRandomWalk` - The hyperfinite random walk construction
* `LoebMeasure` - Loeb's construction of σ-additive measures
* `QuadraticVariation` - Proof that quadratic variation equals t

## Main Results

* Hyperfinite walks have quadratic variation t (up to infinitesimals)
* The standard part of a hyperfinite walk is a.s. continuous
* Loeb measure on hyperfinite path space equals Wiener measure

## References

* Anderson, R. M. (1976). "A nonstandard representation for Brownian motion and
  Itô integration". Israel J. Math. 25, 15-46.
* Loeb, P. (1975). "Conversion from nonstandard to standard measure spaces and
  applications in probability theory". Trans. Amer. Math. Soc. 211, 113-122.
* Albeverio, S., Fenstad, J.E., Høegh-Krohn, R., Lindstrøm, T. (1986).
  "Nonstandard Methods in Stochastic Analysis and Mathematical Physics".
  Academic Press.
* Cutland, N. (2000). "Loeb Measures in Practice: Recent Advances". Springer.
-/

namespace SPDE.Nonstandard

-- Re-export main definitions
-- (imports above make them available)

end SPDE.Nonstandard

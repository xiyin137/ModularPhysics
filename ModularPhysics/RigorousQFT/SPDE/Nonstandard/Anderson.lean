/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/

import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.RandomWalkMoments
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.MaximalInequality
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.SContinuity
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.SContinuityAS
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.LocalCLT

/-!
# Anderson's Theorem Infrastructure

This module provides the probability theory infrastructure needed for Anderson's theorem,
which states that the pushforward of Loeb measure on hyperfinite random walks under the
standard part map equals Wiener measure.

## Contents

* `RandomWalkMoments` - Second moment E[S_k²] = k and Chebyshev bounds
* `MaximalInequality` - P(max |S_i| > M) ≤ (k+1)²/M²
* `SContinuity` - Increment variance and modulus of continuity bounds
* `SContinuityAS` - S-continuity almost surely via Borel-Cantelli
* `LocalCLT` - Local central limit theorem infrastructure

## Main Results

### Fully Proven (No Sorries)
* `sum_partialSumFin_sq` - Σ S_k² = k · 2^n
* `chebyshev_count`, `chebyshev_prob` - Chebyshev bound
* `maximal_count`, `maximal_prob` - Maximal inequality
* `sum_windowIncrement_sq` - E[(S_{k+h} - S_k)²] = h
* `modulus_bound_prob` - P(max increment > M) ≤ numWindows·h/M²

### Infrastructure (With Sorries for Detailed Calculations)
* `violationProbGlobalThreshold_bound` - P(violation) ≤ 1/C² for Borel-Cantelli
* `levyModulus_implies_S_continuous` - Lévy modulus ⟹ S-continuity
* `S_continuity_loeb_almost_surely` - Main theorem structure
* `local_clt_error_bound` - Binomial → Gaussian convergence

## References

* Anderson, R. M. "A nonstandard representation for Brownian motion and Itô integration" (1976)
* Lévy's modulus of continuity theorem
* Feller, W. "An Introduction to Probability Theory" (local CLT)
-/

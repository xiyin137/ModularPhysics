/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/

import ModularPhysics.RigorousQFT.SPDE.Basic
import ModularPhysics.RigorousQFT.SPDE.BrownianMotion
import ModularPhysics.RigorousQFT.SPDE.StochasticIntegration
import ModularPhysics.RigorousQFT.SPDE.RegularityStructures
import ModularPhysics.RigorousQFT.SPDE.SPDE
import ModularPhysics.RigorousQFT.SPDE.Examples

/-!
# Stochastic Partial Differential Equations

This module provides a rigorous formalization of stochastic PDEs (SPDEs)
and Martin Hairer's theory of regularity structures in Lean 4 using Mathlib.

## Overview

Stochastic PDEs are PDEs driven by random noise, typically space-time white noise.
Many physically important SPDEs are "singular" - the nonlinearities are not
classically defined due to the roughness of the solution.

Martin Hairer's theory of regularity structures (Fields Medal 2014) provides
a systematic framework for making sense of these singular SPDEs.

## Main Files

* `Basic.lean` - Filtrations, adapted processes, martingales
* `BrownianMotion.lean` - Wiener process, cylindrical Wiener process
* `StochasticIntegration.lean` - Itô integral, Itô formula, SDEs
* `RegularityStructures.lean` - Regularity structures, models, reconstruction
* `SPDE.lean` - Abstract SPDEs, solutions, well-posedness
* `Examples/Phi4.lean` - The Φ⁴ model
* `Examples/YangMills2D.lean` - 2D Yang-Mills theory

## Key Concepts

### Regularity Structures

A regularity structure is a triple (A, T, G) where:
- A is an index set (homogeneities)
- T = ⊕_{α ∈ A} T_α is a graded vector space
- G is a structure group acting on T

### Models

A model (Π, Γ) provides:
- Π_x : T → S'(ℝ^d) - reconstruction at each point
- Γ_{xy} : T → T - translation between points

### The Reconstruction Theorem

The reconstruction operator R maps modelled distributions
to actual distributions, recovering classical solutions.

## Physical Applications

### The Φ⁴ Model

The dynamic Φ⁴ model: ∂_t φ = Δφ - φ³ + ξ

This is the stochastic quantization of scalar field theory.
In d = 2, 3 it requires renormalization to be well-defined.

### 2D Yang-Mills Theory

The stochastic Yang-Mills equation: ∂_t A = -d*_A F_A + ξ

This defines Langevin dynamics for the Yang-Mills measure,
a key object in gauge theory and QFT.

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014)
* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
* Chandra, Chevyrev, Hairer, Shen, "Langevin dynamic for the 2D Yang-Mills measure"
* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"

-/

-- All definitions are accessible via their fully qualified names
-- e.g., SPDE.Filtration, SPDE.BrownianMotion, SPDE.RegularityStructure, etc.

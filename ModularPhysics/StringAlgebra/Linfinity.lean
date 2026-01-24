/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringAlgebra.Linfinity.Basic
import ModularPhysics.StringAlgebra.Linfinity.SymmetricCoalgebra
import ModularPhysics.StringAlgebra.Linfinity.Coderivations
import ModularPhysics.StringAlgebra.Linfinity.LInfinityAlgebra
import ModularPhysics.StringAlgebra.Linfinity.Morphisms
import ModularPhysics.StringAlgebra.Linfinity.MaurerCartan
import ModularPhysics.StringAlgebra.Linfinity.Transfer
import ModularPhysics.StringAlgebra.Linfinity.BVAlgebra
import ModularPhysics.StringAlgebra.Linfinity.Formality

/-!
# L∞ Algebras

This module provides the theory of L∞ algebras (strongly homotopy Lie algebras)
and related structures.

## Contents

* `Basic` - Graded modules, Koszul signs, degree shifts
* `SymmetricCoalgebra` - The symmetric coalgebra S(V) with shuffle coproduct
* `Coderivations` - Coderivations on S(V) and the L∞ structure
* `LInfinityAlgebra` - Main L∞ algebra definition and interface
* `Morphisms` - L∞ morphisms and quasi-isomorphisms
* `MaurerCartan` - Maurer-Cartan elements and deformation theory
* `Transfer` - Homotopy transfer theorem
* `BVAlgebra` - BV algebras and cyclic L∞ algebras
* `Formality` - Kontsevich's formality theorem

## Mathematical Background

An L∞ algebra on a graded vector space V consists of multilinear brackets
l_n : V^⊗n → V of degree 2-n satisfying generalized Jacobi identities.

Equivalently, an L∞ structure is a degree 1 square-zero coderivation D
on the reduced symmetric coalgebra S⁺(V[1]).

## References

* Lada, Stasheff - "Introduction to sh Lie algebras for physicists"
* Kontsevich - "Deformation quantization of Poisson manifolds"
* Loday, Vallette - "Algebraic Operads"
-/

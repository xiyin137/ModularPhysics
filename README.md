# ModularPhysics

A work-in-progress rigorous formalization of mathematical physics in Lean 4 with Mathlib. All definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. `axiom` is strictly forbidden.

## Related Repositories

- [PhysicsLogic](https://github.com/xiyin137/PhysicsLogic) — Encodes the logical architecture of theoretical physics in Lean's type system. For parsing physics papers, not rigorous formalization.
- [OSreconstruction](https://github.com/xiyin137/OSreconstruction) — Wightman axioms, Osterwalder-Schrader reconstruction, and von Neumann algebra infrastructure.

## Structure

```
ModularPhysics/
├── RigorousQFT/
│   └── SPDE/
│       ├── EKMS/
│       ├── Examples/
│       ├── Helpers/
│       ├── Nonstandard/
│       │   ├── Anderson/
│       │   ├── Foundation/
│       │   └── LoebMeasure/
│       ├── Probability/
│       └── RegularityStructures/
│           ├── Models/
│           └── Trees/
├── StringAlgebra/
│   ├── Linfinity/
│   ├── MZV/
│   └── VOA/
├── StringGeometry/
│   ├── RiemannSurfaces/
│   │   ├── Analytic/
│   │   │   ├── Applications/
│   │   │   │   └── Helpers/
│   │   │   ├── Helpers/
│   │   │   ├── HodgeTheory/
│   │   │   │   ├── Helpers/
│   │   │   │   └── Infrastructure/
│   │   │   ├── Jacobian/
│   │   │   │   └── Helpers/
│   │   │   └── Moduli/
│   │   ├── Combinatorial/
│   │   │   └── Helpers/
│   │   ├── GAGA/
│   │   │   ├── AlgebraicCurves/
│   │   │   │   ├── Cohomology/
│   │   │   │   └── Core/
│   │   │   ├── Bridge/
│   │   │   ├── Cohomology/
│   │   │   │   └── Helpers/
│   │   │   ├── Helpers/
│   │   │   └── Moduli/
│   │   ├── Helpers/
│   │   ├── SchemeTheoretic/
│   │   │   ├── Cohomology/
│   │   │   ├── Helpers/
│   │   │   └── Sheaves/
│   │   └── Topology/
│   ├── Supermanifolds/
│   │   ├── FPS/
│   │   ├── Helpers/
│   │   └── Sheaves/
│   └── SuperRiemannSurfaces/
└── Topology/
    ├── Homotopy/
    ├── Sheaves/
    └── Spectra/
```

**Note:** The `RigorousQFT/Wightman/` and `RigorousQFT/vNA/` subfolders are outdated copies kept for reference. Active development is in [OSreconstruction](https://github.com/xiyin137/OSreconstruction).

### StringGeometry

Develops mathematical foundations for string theory geometry. Current focus is on developing infrastructure of Riemann surfaces, definition of supermanifolds, integration, and super Riemann surfaces; moduli theory to be developed later.

### StringAlgebra

At a beginning stage with many placeholder definitions. Covers L-infinity algebras, multiple zeta values, and vertex operator algebras. Current focus is on developing L-infinity algebra and the Batalin-Vilkovisky formalism.

### RigorousQFT

Stochastic PDE methods for constructive QFT. The Wightman axioms, Osterwalder-Schrader reconstruction, and von Neumann algebra infrastructure have been moved to [OSreconstruction](https://github.com/xiyin137/OSreconstruction).

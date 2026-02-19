# ModularPhysics

A work-in-progress rigorous formalization of mathematical physics in Lean 4 with Mathlib. All definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. `axiom` is strictly forbidden.

## Related Repositories

- [StringGeometry](https://github.com/xiyin137/StringGeometry) — Riemann surfaces, supermanifolds, super Riemann surfaces, and topology infrastructure.
- [StringAlgebra](https://github.com/xiyin137/StringAlgebra) — L-infinity algebras, multiple zeta values, and vertex operator algebras.
- [OSreconstruction](https://github.com/xiyin137/OSreconstruction) — Wightman axioms, Osterwalder-Schrader reconstruction, and von Neumann algebra infrastructure.
- [PhysicsLogic](https://github.com/xiyin137/PhysicsLogic) — Logical architecture of theoretical physics. For parsing physics papers, not rigorous formalization.

## Structure

```
ModularPhysics/
└── RigorousQFT/
    └── SPDE/
        ├── EKMS/
        ├── Examples/
        ├── Helpers/
        ├── Nonstandard/
        │   ├── Anderson/
        │   ├── Foundation/
        │   └── LoebMeasure/
        ├── Probability/
        └── RegularityStructures/
            ├── Models/
            └── Trees/
```

### RigorousQFT

Stochastic PDE methods for constructive QFT, including Itô calculus, regularity structures, and nonstandard analysis approaches. The von Neumann algebra and Wightman axiom infrastructure has been moved to [OSreconstruction](https://github.com/xiyin137/OSreconstruction).

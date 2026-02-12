# ModularPhysics

A work-in-progress formalization of physics in Lean 4 with Mathlib.

## Philosophy

The project explores how physical theories can be expressed in a formal proof assistant. The `Core/` module captures the logical structure of physics using Lean's type system, while `StringGeometry/`, `StringAlgebra/`, `RigorousQFT/`, and `Topology/` pursue rigorous mathematical foundations.

In `Core/`, physical principles are encoded as axioms bundled into structures. At the moment its use is to parse the logical content of physics papers and to explore the interrelations between different physical frameworks without requiring complete mathematical foundations. Note that the use of "axiom" in the Lean environment is risky; while "axiom" is tolerated for now, eventually we will replace all "axiom" with "structure" or "def".

In `StringGeometry/`, `StringAlgebra/`, `RigorousQFT/`, and `Topology/`, the goal is different: all definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. Here "axiom" is strictly forbidden.

## Structure

```
ModularPhysics/
├── Core/
│   ├── ClassicalFieldTheory/
│   ├── ClassicalMechanics/
│   ├── FluidMechanics/
│   ├── GeneralRelativity/
│   ├── QFT/
│   │   ├── AQFT/
│   │   ├── BV/
│   │   ├── CFT/
│   │   │   ├── Bootstrap/
│   │   │   └── TwoDimensional/
│   │   ├── Euclidean/
│   │   ├── KontsevichSegal/
│   │   ├── PathIntegral/
│   │   ├── RG/
│   │   ├── Smatrix/
│   │   ├── TQFT/
│   │   └── Wightman/
│   ├── Quantum/
│   ├── QuantumInformation/
│   ├── SpaceTime/
│   └── Symmetries/
├── Papers/
│   └── GlimmJaffe/
│       ├── ClusterExpansion/
│       ├── Griffiths/
│       ├── Hypercontractivity/
│       └── ReflectionPositivity/
├── RigorousQFT/
│   ├── SPDE/
│   │   ├── EKMS/
│   │   ├── Examples/
│   │   ├── Helpers/
│   │   ├── Nonstandard/
│   │   │   ├── Anderson/
│   │   │   ├── Foundation/
│   │   │   └── LoebMeasure/
│   │   ├── Probability/
│   │   └── RegularityStructures/
│   │       ├── Models/
│   │       └── Trees/
│   ├── Wightman/
│   │   ├── Groups/
│   │   ├── NuclearSpaces/
│   │   ├── Reconstruction/
│   │   └── Spacetime/
│   └── vNA/
│       ├── Bochner/
│       ├── MeasureTheory/
│       ├── Spectral/
│       │   └── Helpers/
│       └── Unbounded/
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

### StringGeometry

Develops mathematical foundations for string theory geometry. Current focus is on developing infrastructure of Riemann surfaces, definition of supermanifolds, integration, and super Riemann surfaces; moduli theory to be developed later.

### StringAlgebra

At a beginning stage with many placeholder definitions. Covers L-infinity algebras, multiple zeta values, and vertex operator algebras. Current focus is on developing L-infinity algebra and the Batalin-Vilkovisky formalism.

### RigorousQFT

Covers the Wightman axioms, von Neumann algebras, and stochastic PDE methods for constructive QFT. Current focus is on developing functional analysis infrastructure, stochastic differential equations, and establishing the Osterwalder-Schrader reconstruction theorem.

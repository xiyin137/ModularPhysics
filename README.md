# ModularPhysics

A work-in-progress formalization of physics in Lean 4 with Mathlib.

## Philosophy

The project has two strictly separate components:

**Rigorous mathematics** (`StringGeometry/`, `StringAlgebra/`, `RigorousQFT/`, `Topology/`): All definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. `axiom` is strictly forbidden.

**Physics paper parsing** (`PhysicsLogic/`): Encodes the logical structure of physics using Lean's type system — making all assumptions explicit and visible as structure fields. This is NOT rigorous mathematical formalization; it is a tool for parsing the logical content of physics papers and exploring interrelations between different physical frameworks. The module contains zero Lean `axiom` declarations — every physical assumption is a field in a `structure`, so the reader can see exactly what each framework presupposes.

## Structure

```
ModularPhysics/
├── PhysicsLogic/                    # NOT rigorous math — physics paper parsing
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
│   ├── Symmetries/
│   └── Papers/                      # Physics paper formalizations (non-rigorous)
│       └── GlimmJaffe/
│           ├── ClusterExpansion/
│           ├── Griffiths/
│           ├── Hypercontractivity/
│           └── ReflectionPositivity/
├── RigorousQFT/                     # Rigorous formalization
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
├── StringAlgebra/                   # Rigorous formalization
│   ├── Linfinity/
│   ├── MZV/
│   └── VOA/
├── StringGeometry/                  # Rigorous formalization
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
└── Topology/                        # Rigorous formalization
    ├── Homotopy/
    ├── Sheaves/
    └── Spectra/
```

**Note:** The `RigorousQFT/Wightman/` and `RigorousQFT/vNA/` subfolders have been refactored into a separate repository: [OSreconstruction](https://github.com/xiyin137/OSreconstruction). The copies in this repo are outdated and kept only for reference.

### StringGeometry

Develops mathematical foundations for string theory geometry. Current focus is on developing infrastructure of Riemann surfaces, definition of supermanifolds, integration, and super Riemann surfaces; moduli theory to be developed later.

### StringAlgebra

At a beginning stage with many placeholder definitions. Covers L-infinity algebras, multiple zeta values, and vertex operator algebras. Current focus is on developing L-infinity algebra and the Batalin-Vilkovisky formalism.

### RigorousQFT

Stochastic PDE methods for constructive QFT. The Wightman axioms, Osterwalder-Schrader reconstruction, and von Neumann algebra infrastructure have been moved to [OSreconstruction](https://github.com/xiyin137/OSreconstruction).

### PhysicsLogic

Encodes the logical architecture of theoretical physics — what each framework assumes and how different frameworks relate. This is for parsing physics papers, not for rigorous mathematical proof. Includes `Papers/` subfolder with formalizations of specific physics papers (Glimm-Jaffe, AMPS, Bell, etc.).

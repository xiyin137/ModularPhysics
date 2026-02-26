# ModularPhysics

`ModularPhysics` is now a lightweight coordination repo after the monorepo split.
Core development happens in sibling repositories in the parent directory.

## Local Sibling Repo Layout

Current local structure (relative to this repo):

| Local path | Repository | Role |
|---|---|---|
| `../StochasticPDE` | [StochasticPDE](https://github.com/xiyin137/StochasticPDE) | Stochastic analysis and SPDE formalization (Ito calculus, regularity structures, nonstandard path). |
| `../stringgeometry` (`../StringGeometry`) | [StringGeometry](https://github.com/xiyin137/StringGeometry) | Umbrella integration repo for split string geometry components. |
| `../stringalgebra` (`../StringAlgebra`) | [StringAlgebra](https://github.com/xiyin137/StringAlgebra) | Split-control/orchestration repo for algebraic domain repos (MZV, VOA, Linfinity, MTC). |
| `../OSReconstruction` | [OSreconstruction](https://github.com/xiyin137/OSreconstruction) | Osterwalder-Schrader reconstruction and operator-algebra foundations. |
| `../Phi4` | [Phi4](https://github.com/xiyin137/Phi4) | Constructive `phi^4_2` QFT pipeline (finite volume -> OS axioms -> reconstruction). |
| `../PhysicsLogic` | [PhysicsLogic](https://github.com/xiyin137/PhysicsLogic) | Logical architecture of physics frameworks and assumption tracking in Lean. |

These are sibling git repositories, not git submodules of `ModularPhysics`.

## Expanded Repository Notes

### StochasticPDE

[StochasticPDE](https://github.com/xiyin137/StochasticPDE) is the main rigorous stochastic-analysis branch of the split ecosystem.

- Scope: Ito calculus, Brownian motion, stochastic integration, Kolmogorov-Chentsov continuity, regularity structures, and singular SPDE interfaces.
- Current README snapshot reports roughly `52,000` lines across `99` Lean files, with an audited Ito-critical path and no named axioms.
- The `ItoCalculus/` stack is self-contained relative to Mathlib and includes a fully proven Ito formula path plus supporting L2/isometry/QV infrastructure.
- Additional tracks include `RegularityStructures/`, `SPDE` examples, `EKMS/`, and a nonstandard-analysis Brownian-motion construction.

### StringGeometry

[StringGeometry](https://github.com/xiyin137/StringGeometry) is an umbrella integration repo that pins and composes three active split repos:

- [stringgeometry-supermanifolds](https://github.com/xiyin137/stringgeometry-supermanifolds)
- [stringgeometry-riemann-surfaces](https://github.com/xiyin137/stringgeometry-riemann-surfaces)
- [stringgeometry-super-riemann-surfaces](https://github.com/xiyin137/stringgeometry-super-riemann-surfaces)

Primary responsibility is dependency pinning, aggregate imports, and split-architecture tooling/docs.

### StringAlgebra

[StringAlgebra](https://github.com/xiyin137/StringAlgebra) is the split-control repo for algebraic tracks. Main domain development is in dedicated repos:

- [StringAlgebra-MZV](https://github.com/xiyin137/StringAlgebra-MZV)
- [StringAlgebra-VOA](https://github.com/xiyin137/StringAlgebra-VOA)
- [StringAlgebra-Linfinity](https://github.com/xiyin137/StringAlgebra-Linfinity)
- [StringAlgebra-MTC](https://github.com/xiyin137/StringAlgebra-MTC)

This repo keeps split planning, extraction scripts, and policy/checklist documentation.

### OSreconstruction

[OSreconstruction](https://github.com/xiyin137/OSreconstruction) develops the OS <-> Wightman bridge with supporting infrastructure:

- `OSReconstruction.Wightman`
- `OSReconstruction.SCV`
- `OSReconstruction.ComplexLieGroups`
- `OSReconstruction.vNA`

It also serves as a core dependency layer for downstream constructive-QFT projects.

### Phi4

[Phi4](https://github.com/xiyin137/Phi4) targets Lean formalization of constructive two-dimensional `phi^4` Euclidean QFT, including:

1. finite-volume construction,
2. infinite-volume limit,
3. OS axiom packaging,
4. reconstruction-facing interfaces.

The project tracks explicit theorem-level proof gaps while maintaining no named axioms and a buildable core target.

### PhysicsLogic

[PhysicsLogic](https://github.com/xiyin137/PhysicsLogic) focuses on representing the logical structure of physics, rather than full from-first-principles formal proof of each analytic component.

- Goal: encode assumptions, implications, and framework interfaces directly in Lean types.
- Coverage: spacetime/symmetry foundations, classical physics modules, quantum and quantum information, and broad QFT architecture (Wightman, OS, AQFT, RG, BV, CFT, TQFT, etc.).
- Includes paper-specific formalization tracks (`Bell`, `AMPS`, `Phi4_2D`, `cTheorem`, `VafaWitten`, and others).
- Design policy emphasizes explicit assumptions and disallows hidden axiom-smuggling patterns.

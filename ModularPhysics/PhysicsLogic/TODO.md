# PhysicsLogic Module TODO — Architectural Review & Roadmap

(Formerly `Core/` — renamed to avoid confusion with rigorous formalization modules.)

## Vision

PhysicsLogic encodes the **logical architecture of theoretical physics** — making assumptions, structures, and inter-framework relationships explicit in Lean's type system. It is NOT about mathematical rigor (that belongs in RigorousQFT, StringGeometry, etc.) but about illuminating **what physics assumes and how different frameworks relate**. This module is for parsing physics papers, not for rigorous mathematical formalization.

Eliminating `axiom` and using `structure`/`def`/`variable` is essential because Lean axioms silently introduce assumptions invisible to the reader — the opposite of the project's goal.

---

## Current Status

### QFT Module: COMPLETE (0 axioms)

All ~273 axioms eliminated across ~40 files in the QFT/ directory. Every submodule builds cleanly.

| Submodule | Axioms Eliminated | Files | Status |
|-----------|------------------|-------|--------|
| PathIntegral/ | 65 | 8 | Done |
| Euclidean/ | 7 | 4 | Done |
| AQFT/ | 29 | 4 | Done |
| RG/ | 6 | 4 | Done |
| BV/ | 8 | 2 | Done |
| Smatrix/ | 35 | 4 | Done |
| TQFT/ | 17 | 5 | Done |
| CFT/Basic.lean | 18 | 1 | Done |
| CFT/Bootstrap/ | 46 | 3 | Done |
| CFT/TwoDimensional/ | 42 | 5 | Done |

**Pattern applied throughout**:
- `axiom fooTheoryD : FooTheory` → delete axiom; keep structure; downstream takes theory as parameter
- `data : Unit` → proper fields with meaningful content (operators, tensors, evaluation maps)
- `True` placeholders → meaningful conditions (`≠ 0`, `≥ 1`, `≠ []`, `Nonempty`, etc.)
- Forwarding defs/theorems referencing deleted axioms → deleted
- Structures referencing data from other structures → parameterized by dependencies

### Other Modules: CLEAN (0 axioms)

Verified via `grep -r "^axiom" ModularPhysics/PhysicsLogic/`: zero axioms across the entire PhysicsLogic directory, including all non-QFT modules (ClassicalMechanics, Quantum, SpaceTime, Symmetries, StatisticalMechanics, Thermodynamics, Condensed, Information).

---

## Remaining Issues

### Issue 2: Fix remaining `True` placeholders
Some `True` placeholders remain where the full statement requires infrastructure not yet available (e.g., nested Virasoro bracket computations in `VirasoroAlgebra.jacobi`). These are documented with comments.

### Issue 3: Fix remaining `Unit` data fields
`VirasoroGeneratorElement` and `AntiVirasoroGeneratorElement` intentionally keep `data : Unit` since they are formal generators of an abstract Lie algebra — the index `n : ℤ` is the meaningful data.

### Issue 4: Review sorry count
The `t_dual` definition in `CFT/TwoDimensional/Examples.lean` has a sorry for the weight proof (T-duality swaps momentum/winding). This is acceptable for PhysicsLogic but could be proved with some algebraic manipulation.

---

## Design Principle

**Every module should follow the Wightman pattern:**

| Aspect | Wightman (Good) | Old AQFT (Bad, now fixed) |
|--------|----------------|--------------------------|
| Lean axioms | 0 | 29+ → 0 |
| Physical assumptions | Structure fields | Hidden in global axioms |
| Spacelike separation | Minkowski computation | `True` placeholder |
| Poincaré group | Imports from Symmetries | `Unit` type |
| Reader sees assumptions? | Yes | No |

The Wightman module demonstrates that you can encode all physical axioms as structure fields without using a single Lean `axiom`. This is now the standard across all of QFT.

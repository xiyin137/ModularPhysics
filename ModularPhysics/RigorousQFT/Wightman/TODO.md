# Wightman QFT Module — TODO

## TOP PRIORITY: OS Reconstruction Theorems

**Key insight**: Nuclear spaces / Minlos are NOT needed for the OS reconstruction theorems.
The reconstruction takes Schwinger functions as given input — nuclear spaces are about
*constructing* those Schwinger functions (upstream), not about reconstructing Wightman QFT.

### Critical Path for OS Reconstruction

1. **Fix OSLinearGrowthCondition definition** (sorry in definition! — line 499)
2. **Schwartz tensor product** → blocks WightmanInnerProduct, fieldOperatorAction
3. **GNS construction steps** → borchersSetoid.trans, PreHilbertSpace.innerProduct
4. **wightman_to_os** (R→E, easier direction via Wick rotation)
5. **os_to_wightman** (E'→R', the hard theorem — analytic continuation + E0')

### What Does NOT Block Reconstruction

- Nuclear operator properties (NuclearOperator.lean)
- Nuclear space closure properties (NuclearSpace.lean)
- Schwartz nuclearity (SchwartzNuclear.lean)
- Bochner-Minlos theorems (BochnerMinlos.lean)
- Free field measure (EuclideanMeasure.lean)

These are needed for *constructive QFT* (building concrete examples of Schwinger functions)
but not for the OS reconstruction theorems themselves.

## Status Overview

| File | Sorrys | Status |
|------|--------|--------|
| Basic.lean | 0 | Complete |
| Groups/Lorentz.lean | 0 | Complete |
| Groups/Poincare.lean | 0 | Complete |
| Spacetime/Metric.lean | 0 | Complete |
| WightmanAxioms.lean | 1 | WightmanDistribution needs tensor product |
| OperatorDistribution.lean | 1 | momentum_eq_generator (Stone theorem, not blocking) |
| **Reconstruction.lean** | **12** | **TOP PRIORITY** |
| NuclearSpaces/NuclearOperator.lean | 4 | Deferred (not blocking reconstruction) |
| NuclearSpaces/NuclearSpace.lean | 4 | Deferred |
| NuclearSpaces/BochnerMinlos.lean | 6 | Deferred |
| NuclearSpaces/SchwartzNuclear.lean | 7 | Deferred |
| NuclearSpaces/EuclideanMeasure.lean | 6 | Deferred |
| **Total** | **~39** | |

## Reconstruction.lean Sorry Breakdown (12 sorrys)

### Infrastructure (blocking)
- `OSLinearGrowthCondition.growth_estimate`: **Sorry in definition!** Replace with Schwartz seminorm
- `WightmanInnerProduct`: Needs tensor product f̄_m ⊗ g_{n-m}
- `fieldOperatorAction`: Needs tensor product (prepend f to sequence)

### GNS Construction
- `borchersSetoid.trans`: Transitivity (Cauchy-Schwarz)
- `PreHilbertSpace.innerProduct`: Well-definedness on quotient (Cauchy-Schwarz)
- `fieldOperator`: Well-definedness on quotient

### Main Theorems
- `wightman_reconstruction`: Full GNS → WightmanQFT
- `wightman_uniqueness`: Uniqueness up to unitary equivalence

### OS Bridge (the main goal)
- `wightman_to_os` (R→E): Wick rotation, straightforward
- `os_to_wightman` (E'→R'): **THE HARD THEOREM** — needs:
  - Pre-Hilbert space from E2 (reflection positivity)
  - Contraction semigroup from E0'+E1
  - Inductive analytic continuation (OS II Thm 4.1-4.2)
  - Boundary values → Wightman distributions (E0' essential)
  - Verify R0-R5

### WightmanFunctions.spectrum_condition (2 sorrys)
- Holomorphicity in ForwardTube (dependent type)
- Boundary values of analytic continuation

## Architecture (Reconstruction Focus)

```
Layer 0 (DONE): Metric, Lorentz, Poincare, Basic — 0 sorrys
    ↓
OperatorDistribution.lean ──> WightmanAxioms.lean
    ↓                              ↓
    └──────────> Reconstruction.lean ←── NEW: TensorProduct infrastructure
                     ↓
              os_to_wightman (E'→R')  ←── NEW: AnalyticContinuation infrastructure
              wightman_to_os (R→E)
```

Nuclear spaces / Minlos are a SEPARATE development line for constructive QFT.

## Key Mathematical References

- **OS I**: "Reconstruction theorem I.pdf" — Theorem R→E (§5), Theorem E→R (§4)
  - Note: Lemma 8.8 has a gap (fixed in OS II)
- **OS II**: "reconstruction theorem II.pdf" — Linear growth E0' (§IV.1),
  analytic continuation (§V), temperedness estimates (§VI)

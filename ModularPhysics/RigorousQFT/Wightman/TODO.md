# Wightman QFT Module — TODO

## TOP PRIORITY: OS Reconstruction Theorems

**Key insight**: Nuclear spaces / Minlos are NOT needed for the OS reconstruction theorems.
The reconstruction takes Schwinger functions as given input — nuclear spaces are about
*constructing* those Schwinger functions (upstream), not about reconstructing Wightman QFT.

### Critical Path for OS Reconstruction

1. **Schwartz tensor product sorrys** → smooth'/decay' for conjTensorProduct, prependField
2. **Field operator well-definedness** → fieldOperator quotient lift
3. **wightman_to_os** (R→E, needs BHW + analytic continuation)
4. **os_to_wightman** (E'→R', the hard theorem — analytic continuation + E0')

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
| SchwartzTensorProduct.lean | 10 | Schwartz smooth'/decay' for tensor ops |
| **Reconstruction.lean** | **5** | Core theorems + field operator |
| **Reconstruction/AnalyticContinuation.lean** | **14** | NEW: Tube domains, BHW, edge-of-wedge |
| **Reconstruction/GNSConstruction.lean** | **5** | NEW: Vacuum, field ops, GNS property |
| **Reconstruction/WickRotation.lean** | **24** | NEW: OS↔Wightman bridge |
| NuclearSpaces/NuclearOperator.lean | 4 | Deferred (not blocking reconstruction) |
| NuclearSpaces/NuclearSpace.lean | 4 | Deferred |
| NuclearSpaces/BochnerMinlos.lean | 6 | Deferred |
| NuclearSpaces/SchwartzNuclear.lean | 8 | Deferred |
| NuclearSpaces/EuclideanMeasure.lean | 6 | Deferred |
| **Total** | **~88** | |

## Recent Progress

### Proven (no sorry)
- `WightmanInnerProduct_hermitian` — Hermiticity of inner product ⟨F,G⟩ = conj(⟨G,F⟩)
- `null_inner_product_zero` — Null vector annihilation ⟨X,X⟩.re=0 → ⟨X,Y⟩=0
- `PreHilbertSpace.innerProduct` — Well-definedness on quotient (via Cauchy-Schwarz)
- `borchersSetoid.trans` — Transitivity of GNS equivalence relation
- `preHilbert_inner_pos` — Positive semi-definiteness on quotient
- `preHilbert_inner_real` — Inner product real on diagonal
- `schwartzToOnePoint` — Via compCLMOfContinuousLinearEquiv (no more sorry!)
- `fieldOperatorAction` — Borchers sequence level (uses prependField)
- Full sesquilinearity infrastructure (add, smul, neg, sub in both arguments)

### Infrastructure Created (with sorrys for proofs)
- `Reconstruction/AnalyticContinuation.lean` — ComplexLorentzGroup, tube domains,
  Bargmann-Hall-Wightman, edge-of-the-wedge, Jost lemma, SchwingerFromWightman
- `Reconstruction/GNSConstruction.lean` — Vacuum sequence, field operator properties,
  GNS reproduces Wightman functions
- `Reconstruction/WickRotation.lean` — constructSchwingerFunctions, OS↔Wightman bridge,
  EuclideanSemigroup, AnalyticContinuationRegion, constructWightmanFunctions,
  IsWickRotationPair, wightman_to_os_full, os_to_wightman_full

## Reconstruction.lean Sorry Breakdown (5 sorrys)

### Field Operator
- `fieldOperator`: Well-definedness on quotient (needs null vector preservation)

### Main Theorems
- `wightman_reconstruction`: Full GNS → WightmanQFT + reproduces Wightman functions
- `wightman_uniqueness`: Uniqueness up to unitary equivalence

### OS Bridge
- `wightman_to_os` (R→E): Produces OS axioms with analytic continuation on forward tube
- `os_to_wightman` (E'→R'): Produces Wightman functions from OS axioms + linear growth

## AnalyticContinuation.lean Sorry Breakdown (14 sorrys)

### Complex Lorentz Group
- `ComplexLorentzGroup.ofReal`: metric_preserving, proper, orthochronous
- `ComplexLorentzGroup.ofEuclidean`: metric_preserving, proper, orthochronous

### Tube Domains
- `euclidean_ordered_in_forwardTube`: Ordered Euclidean points in forward tube
- `euclidean_distinct_in_permutedTube`: Distinct Euclidean points in permuted tube

### Key Theorems
- `edge_of_the_wedge`: Bogoliubov's theorem
- `bargmann_hall_wightman`: Extension to permuted extended tube
- `jost_lemma`: Spacelike commutativity at Jost points
- `schwinger_euclidean_invariant`, `schwinger_permutation_symmetric`

## WickRotation.lean Sorry Breakdown (24 sorrys)

### OS↔Wightman Construction
- `constructedSchwinger_symmetric`: BHW permutation symmetry
- `constructedSchwinger_cluster`: Cluster property
- `osPreHilbertSpace`: 10 sorrys (WightmanFunctions construction from OS data)
- `AnalyticContinuationRegion`: Definition correct, sorrys in theorems using it
- `inductive_analytic_continuation`: OS II Theorem 4.1
- `full_analytic_continuation`: Forward tube reached after d+1 steps
- `boundary_values_tempered`: E0' ensures tempered boundary values
- `constructWightmanFunctions`: 7 fields sorry'd (normalized through hermitian)
- `wightman_to_os_full`, `os_to_wightman_full`: Wick rotation pair property

## Architecture

```
Layer 0 (DONE): Metric, Lorentz, Poincare, Basic — 0 sorrys
    ↓
OperatorDistribution.lean ──> WightmanAxioms.lean
    ↓                              ↓
    └──────────> Reconstruction.lean ←── SchwartzTensorProduct.lean
                     ↓
              Reconstruction/AnalyticContinuation.lean  (tube domains, BHW)
              Reconstruction/GNSConstruction.lean       (vacuum, field ops)
              Reconstruction/WickRotation.lean          (OS↔Wightman bridge)
```

Nuclear spaces / Minlos are a SEPARATE development line for constructive QFT.

## Key Mathematical References

- **OS I**: "Reconstruction theorem I.pdf" — Theorem R→E (§5), Theorem E→R (§4)
  - Note: Lemma 8.8 has a gap (fixed in OS II)
- **OS II**: "reconstruction theorem II.pdf" — Linear growth E0' (§IV.1),
  analytic continuation (§V), temperedness estimates (§VI)
- **Streater-Wightman**: "PCT, Spin and Statistics, and All That" — Chapter 3
- **Glimm-Jaffe**: "Quantum Physics" — Chapter 19 (reconstruction)

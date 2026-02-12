# Wightman QFT Module — TODO

## Status Overview

| File | Sorrys | Status |
|------|--------|--------|
| Basic.lean | 0 | Complete |
| Groups/Lorentz.lean | 0 | Complete |
| Groups/Poincare.lean | 0 | Complete |
| Spacetime/Metric.lean | 0 | Complete |
| WightmanAxioms.lean | 1 | Definitions complete; 1 sorry in `momentum_eq_generator` |
| OperatorDistribution.lean | 1 | Definitions complete; 1 sorry |
| Reconstruction.lean | 12 | Main theorems stated; proofs need infrastructure |
| NuclearSpaces/NuclearOperator.lean | 5 | Core definitions proven; some properties sorry'd |
| NuclearSpaces/NuclearSpace.lean | 4 | Definition + NuclearFrechet complete; closure properties sorry'd |
| NuclearSpaces/BochnerMinlos.lean | 7 | Bochner + Minlos stated; proofs sorry'd |
| NuclearSpaces/SchwartzNuclear.lean | 7 | S(R^n) nuclear stated; Hermite infrastructure sorry'd |
| NuclearSpaces/EuclideanMeasure.lean | 2 | Free field measure connected to Minlos; 2 sorrys |
| **Total** | **39** | |

## Sorry Breakdown by File

### Reconstruction.lean (12 sorrys)

Core OS reconstruction infrastructure:

- `WightmanInnerProduct`: Tensor product f_m tensor g_{n-m} in SchwartzNPoint
- `borchersSetoid.trans`: Transitivity of GNS equivalence (needs Cauchy-Schwarz)
- `PreHilbertSpace.innerProduct` well-definedness: Quotient compatibility
- `spectrum_condition` (2): Holomorphicity + boundary values of analytic continuation
- `fieldOperatorAction`: Tensor product construction for field operators
- `fieldOperator` well-definedness: Respects Borchers equivalence
- `wightman_reconstruction`: Main reconstruction theorem
- `wightman_uniqueness`: Uniqueness up to unitary equivalence
- `wightman_to_os`: Wightman -> Schwinger functions (Wick rotation)
- `os_to_wightman`: OS axioms + linear growth -> Wightman (analytic continuation)
- `OSLinearGrowthCondition.growth_estimate`: Sobolev norm formula

### WightmanAxioms.lean (1 sorry)

- `momentum_eq_generator`: Stone theorem generator = momentum operator

### OperatorDistribution.lean (1 sorry)

- `momentum_eq_generator`: Same as above (uniqueness of limits)

### NuclearSpaces/NuclearOperator.lean (5 sorrys)

- `IsNuclearOperator.add` (2): Interleaved summability + HasSum for sum of nuclear ops
- `isCompactOperator`: Nuclear => compact (finite-rank approximation)
- `opNorm_le_nuclearNorm`: ||T|| <= ||T||_1 (norm bound from representation)
- `toNuclearRepresentation`: Hilbert SVD orthonormality bound

### NuclearSpaces/NuclearSpace.lean (4 sorrys)

- `finiteDimensional`: Finite-dim spaces are nuclear
- `subspace_nuclear`: Closed subspaces of nuclear spaces are nuclear
- `product_nuclear`: Countable products of nuclear spaces are nuclear
- `NuclearFrechet.toNuclearSpace`: Nuclear Frechet presentation => NuclearSpace class

### NuclearSpaces/BochnerMinlos.lean (7 sorrys)

- `conj_neg`: Positive-definite => phi(-x) = conj(phi(x))
- `norm_le_eval_zero`: Positive-definite => |phi(x)| <= phi(0)
- `bochner_theorem`: Bochner's theorem (finite-dim, needs Fourier inversion)
- `minlos_theorem`: Minlos' theorem (nuclearity => tightness => Kolmogorov extension)
- `minlos_unique`: Uniqueness of Minlos measure
- `gaussianCharacteristicFunctional_posdef`: Gaussian exp(-1/2 <f,Af>) is positive-definite
- `freeFieldCharacteristic`: Placeholder definition (returns sorry)

### NuclearSpaces/SchwartzNuclear.lean (7 sorrys)

- `schwartzSeminorm_mono`: Seminorm monotonicity p_{k1,l1} <= p_{k2,l2}
- `nuclearFrechet` (3): seminorms_mono, separating, nuclear_step (Hermite expansion)
- `hermiteFunction_schwartz`: Hermite functions are Schwartz
- `hermiteFunction_orthonormal`: L^2 orthonormality
- `hermiteFunction_seminorm_decay`: Rapid decay p_{k,l}(h_m) <= C * m^{-N}

### NuclearSpaces/EuclideanMeasure.lean (2 sorrys)

- `FreeFieldCharacteristic_posdef`: exp(-1/2 Q(f)) is positive-definite
- `schwingerTwoPoint_eq_bilinear`: S_2(f,g) = B(f,g) (moment calculation)

## Priority Roadmap

### High Priority (Blocking main results)

1. **Tensor product infrastructure** for Reconstruction.lean
   - Need proper tensor product of Schwartz test functions
   - Blocks: WightmanInnerProduct, fieldOperatorAction, reconstruction theorem

2. **Minlos' theorem proof** (BochnerMinlos.lean)
   - Finite-dim Bochner (Fourier inversion)
   - Projective family from characteristic functional
   - Nuclearity => tightness (the key step)
   - Kolmogorov extension

3. **Hermite function theory** (SchwartzNuclear.lean)
   - Hermite functions in Schwartz space
   - Orthonormality in L^2
   - Seminorm decay estimates
   - Blocks: S(R^n) nuclearity proof

### Medium Priority (Core infrastructure)

4. **Nuclear operator properties** (NuclearOperator.lean)
   - Sum of nuclear operators (interleaving)
   - Nuclear => compact
   - Operator norm <= nuclear norm

5. **Nuclear space closure properties** (NuclearSpace.lean)
   - Finite-dimensional, subspace, product nuclearity
   - NuclearFrechet => NuclearSpace

6. **Positive-definite function theory** (BochnerMinlos.lean)
   - conj_neg, norm_le_eval_zero
   - Gaussian positivity

### Lower Priority (Can be deferred)

7. **Reconstruction.lean main proofs**
   - GNS construction, field operators, reconstruction
   - These are deep results depending on all infrastructure above

8. **OS <-> Wightman bridge**
   - wightman_to_os, os_to_wightman
   - Requires analytic continuation + distribution theory

## Architecture

```
Basic.lean ─────────────────┐
Groups/Lorentz.lean ────────┤
Groups/Poincare.lean ───────┤
Spacetime/Metric.lean ──────┤
                            ├──> WightmanAxioms.lean ──> OperatorDistribution.lean
                            │
NuclearSpaces/              │
  NuclearOperator.lean ─────┤
       |                    │
  NuclearSpace.lean ────────┤
       |          \         │
  SchwartzNuclear  BochnerMinlos
       \            /       │
    EuclideanMeasure.lean ──┤
                            │
                            └──> Reconstruction.lean (OS <-> Wightman)
```

# Analytic Folder Development Plan

## Vision

Develop a **self-contained analytic theory** of Riemann surfaces, culminating in a
**pure analytic proof of the Riemann-Roch theorem** via Hodge theory and the dbar-operator.

**Independence Constraint**: Only allowed external imports:
- `Mathlib.*` (always search mathlib for available lemmas and definitions)
- `ModularPhysics.StringGeometry.RiemannSurfaces.Topology.*`

**No imports from**: SchemeTheoretic/, GAGA/, Algebraic/, Combinatorial/

---

## Current State (Feb 2026)

### Folder Structure
```
Analytic/
├── Basic.lean                      # RiemannSurface, CompactRiemannSurface           ✅ 0 sorrys
├── MeromorphicFunction.lean        # AnalyticMeromorphicFunction                     1 sorry
├── Divisors.lean                   # Analytic Divisor, PicardGroup                   ✅ 0 sorrys
├── LineBundles.lean                # HolomorphicLineBundle, LinearSystem             ✅ 0 sorrys
├── RiemannRoch.lean                # Analytic RR (stubs)                             5 sorrys
├── Analytic.lean                   # Re-exports                                      ✅ 0 sorrys
├── HodgeTheory/
│   ├── DifferentialForms.lean      # (p,q)-forms, wedge, conjugation                 ✅ 0 sorrys
│   ├── Dolbeault.lean              # dbar operator, Dolbeault cohomology              1 sorry
│   ├── Harmonic.lean               # Harmonic functions on RS                         3 sorrys
│   ├── HodgeDecomposition.lean     # Hodge decomposition, Dolbeault isomorphism       7 sorrys
│   ├── SerreDuality.lean           # Analytic Serre duality                           4 sorrys
│   ├── Helpers/
│   │   └── HarmonicHelpers.lean    # Coordinate definitions                          ✅ 0 sorrys
│   └── Infrastructure/
│       ├── RealSmoothness.lean     # R-smooth vs C-smooth bridge                     ✅ 0 sorrys
│       ├── WirtingerDerivatives.lean # d/dz and d/dz-bar                             ✅ 0 sorrys
│       ├── MaximumPrinciple.lean   # Maximum principle via circle averages            ✅ 0 sorrys
│       ├── MeanValueConverse.lean  # MVP <=> harmonic                                ✅ 0 sorrys
│       ├── PoissonIntegral.lean    # Schwarz/Poisson integral, boundary values        1 sorry
│       └── HarmonicConjugate.lean  # Harmonic conjugate existence                    1 sorry
├── Jacobian/                       # (lower priority)
│   ├── AbelJacobi.lean             # Abel-Jacobi map                                 7 sorrys
│   ├── ThetaFunctions.lean         # Theta functions                                 6 sorrys
│   └── Helpers/ThetaHelpers.lean   # Theta helpers                                   4 sorrys*
├── Applications/                   # (lower priority)
│   ├── GreenFunction.lean          # Green's function                                5 sorrys
│   └── Helpers/GreenHelpers.lean   # Green helpers                                   ✅ 0 sorrys
└── Moduli/                         # (lower priority)
    ├── Moduli.lean                 # Re-exports                                      ✅ 0 sorrys
    ├── FenchelNielsen.lean         # Fenchel-Nielsen coordinates                     ✅ 0 sorrys
    ├── QuasiconformalMaps.lean     # Quasiconformal maps                             3 sorrys
    └── SiegelSpace.lean            # Siegel upper half-space                         ✅ 0 sorrys
```
*ThetaHelpers has 4 actual sorrys + 3 mentions in comments

### Sorry Count Summary
- **Total**: ~48 actual sorrys across 13 files
- **Core HodgeTheory pipeline**: 17 sorrys (priority)
- **Jacobian/Applications/Moduli**: 25 sorrys (lower priority)
- **Other (MeromorphicFunction, RiemannRoch)**: 6 sorrys

---

## Proven Infrastructure (0 sorrys)

### Foundation
- **Basic.lean**: `RiemannSurface` (connected complex 1-manifold), `CompactRiemannSurface`,
  `RiemannSphere` (full 2-chart atlas), `IsHolomorphic`, `holomorphicIsConstant`
- **Divisors.lean**: `Divisor`, degree, `IsPrincipal`, `PicardGroup`, argument principle
- **LineBundles.lean**: `HolomorphicLineBundle`, `ofDivisor`, `tensor`, `dual`, `degree`,
  `LinearSystem`, `linearSystem_empty_negative_degree`

### Differential Forms & Smoothness
- **DifferentialForms.lean**: `SmoothFunction`, `Form_10/01/11/1`, wedge products,
  conjugation, `HolomorphicForm`, `areaForm`, full C-module structures
- **RealSmoothness.lean**: `contMDiff_real_of_complex_rs` (C-smooth => R-smooth),
  conjugation smoothness, `RealSmoothFunction` ring, re/im extraction
- **WirtingerDerivatives.lean**: `wirtingerDeriv/wirtingerDerivBar`,
  `holomorphic_iff_wirtingerDerivBar_zero`, `laplacian_eq_four_wirtinger_mixed`,
  chain rules, algebraic properties

### Harmonic Analysis
- **MaximumPrinciple.lean**: `eq_of_circleAverage_eq_of_le`,
  `harmonic_maximum_principle_ball/connected`, minimum principle
- **MeanValueConverse.lean**: `SatisfiesMVP`, `harmonicOnNhd_of_mvp`
  (MVP + continuous => harmonic, via Poisson integral)
- **PoissonIntegral.lean** (mostly proven):
  - `schwarzIntegral_differentiableAt` (holomorphic in z)
  - `poissonIntegral_harmonicOnNhd` (Re(holomorphic) = harmonic)
  - `poissonIntegral_boundary_values` (correct boundary values)
  - `mvp_zero_boundary_implies_zero` (MVP + zero boundary => zero)
  - `mvp_implies_harmonicOnNhd` (main theorem, depends on `mvp_eq_poissonIntegral`)
  - `mvp_implies_contDiffOn`, `mvp_implies_laplacian_zero` (corollaries)

---

## Priority Sorrys (Core Pipeline)

### Tier 1: Low-Hanging Fruit (infrastructure in place)

| Sorry | File | What's Needed |
|-------|------|--------------|
| `mvp_eq_poissonIntegral` | PoissonIntegral.lean | h = f - P[f] satisfies MVP, h=0 on boundary, max principle => h=0. All ingredients proven. |
| `harmonic_conjugate_simply_connected` | HarmonicConjugate.lean | Poincare lemma / homotopy invariance of curve integrals |

### Tier 2: Hodge Theory Core

| Sorry | File | What's Needed |
|-------|------|--------------|
| `local_dbar_poincare` | Dolbeault.lean | Local exactness of dbar (local Cauchy integral formula) |
| `hodge_decomposition_01` | HodgeDecomposition.lean | Hodge decomposition for (0,1)-forms |
| `harmonic_10_closed` | HodgeDecomposition.lean | dbar-closed (1,0)-forms => harmonic |
| `dim_harmonic_10_eq_genus` | HodgeDecomposition.lean | dim H^{1,0} = genus |
| `harmonic_to_deRham_bijective` | HodgeDecomposition.lean | Harmonic forms represent de Rham |
| `l2_inner_product_10_exists` | HodgeDecomposition.lean | L2 inner product existence |
| `orthogonal_to_dbar_image_10` | HodgeDecomposition.lean | Integration by parts |
| `dolbeault_isomorphism` | HodgeDecomposition.lean | Dolbeault isomorphism |

### Tier 3: Serre Duality & Riemann-Roch

| Sorry | File | What's Needed |
|-------|------|--------------|
| `l2_inner_product_exists` | SerreDuality.lean | Integration + metric |
| `surjective_of_serre_duality` | SerreDuality.lean | Riesz representation |
| `residue_sum_zero` | SerreDuality.lean | Stokes' theorem |
| `kodaira_vanishing_kernel_dimension` | SerreDuality.lean | Full Serre duality |
| `canonical_divisor_exists` | RiemannRoch.lean | Meromorphic 1-form existence |
| `atiyah_singer_index_formula` | RiemannRoch.lean | Index theorem |
| `h0_canonical_eq_genus` | RiemannRoch.lean | dim H^0(K) = g |
| `harmonic_10_isomorphic_h0_canonical` | RiemannRoch.lean | Holomorphic 1-forms = K-sections |

### Tier 4: Other

| Sorry | File | What's Needed |
|-------|------|--------------|
| `harmonic_1forms_dimension` | Harmonic.lean | Hodge theory |
| `poisson_dirichlet_existence` | Harmonic.lean | Poisson solution |
| `argument_principle_count` | MeromorphicFunction.lean | Integration / topological degree |
| `linear_system_linear_dependence` | RiemannRoch.lean | Linear dependence criterion |

---

## Proof Strategy: Analytic Riemann-Roch

### Path 1: Via Index Theory (current approach in RiemannRoch.lean)
1. chi(L) = ind(dbar_L) where dbar_L is the twisted Dolbeault operator
2. Homotopy invariance: index depends only on topological data
3. Normalization: chi(O) = 1 - g
4. Degree shift: chi(L(p)) = chi(L) + 1
5. Induction: chi(L) = deg(L) + 1 - g

### Path 2: Via Hodge Theory (alternative)
1. Hodge decomposition => dim H^{p,q} finite
2. Serre duality => h^1(L) = h^0(K tensor L*)
3. chi(O) = h^0(O) - h^1(O) = 1 - g
4. Point exact sequence for degree shift
5. Same induction as Path 1

### Key Dependencies
```
RealSmoothness ──> DifferentialForms ──> Dolbeault ──> HodgeDecomposition
     |                                      |                |
WirtingerDerivs ─────────────────────────────┘          SerreDuality
     |                                                       |
MaximumPrinciple ──> PoissonIntegral ──> MeanValueConverse   |
     |                                      |                |
HarmonicConjugate ──> Harmonic ─────────────┘                |
                                                             v
LineBundles ──────────────────────────────────────────> RiemannRoch
```

---

## Next Steps (Priority Order)

1. **Prove `mvp_eq_poissonIntegral`** - all ingredients in place, completes Poisson chain
2. **Prove `harmonic_conjugate_simply_connected`** - unlocks harmonic infrastructure
3. **Work on Dolbeault `local_dbar_poincare`** - key for cohomology theory
4. **HodgeDecomposition sorrys** - core of the analytic approach
5. **SerreDuality** - needed for classical form of Riemann-Roch
6. **RiemannRoch** - final goal

---

## References

- Griffiths & Harris, "Principles of Algebraic Geometry", Ch 0-1
- Forster, "Lectures on Riemann Surfaces"
- Farkas & Kra, "Riemann Surfaces", Ch III
- Wells, "Differential Analysis on Complex Manifolds"
- Axler, Bourdon, Ramey, "Harmonic Function Theory", Ch 1
- Ahlfors, "Complex Analysis", Ch 6

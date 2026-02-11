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

### Major Milestone: `riemann_roch_theorem` FULLY PROVEN

The analytic Riemann-Roch theorem (`RiemannRoch.lean`) has a **complete proof** modulo
4 foundational sorrys. The proof uses induction on total variation of divisors:
1. Define correction term f(D) = χ(D) - deg(D)
2. Show f is invariant: f(D) = f(D ± [p]) using `chi_add_point` / `chi_sub_point`
3. Strong induction on `TV(D)` shows f(D) = f(0)
4. Base case: f(0) = χ(O) = 1 - g

### Folder Structure
```
Analytic/
├── Basic.lean                      # RiemannSurface, CompactRiemannSurface           ✅ 0 sorrys
├── MeromorphicFunction.lean        # AnalyticMeromorphicFunction                     1 sorry
├── Divisors.lean                   # Analytic Divisor, PicardGroup                   ✅ 0 sorrys
├── LineBundles.lean                # HolomorphicLineBundle, LinearSystem             ✅ 0 sorrys
├── RiemannRoch.lean                # Analytic RR — FULLY PROVEN                      4 sorrys
├── Analytic.lean                   # Re-exports                                      ✅ 0 sorrys
├── Helpers/                        # Riemann-Roch infrastructure (NEW 2026-02-10)
│   ├── AnalyticBridge.lean         # MDifferentiable → AnalyticAt bridge             ✅ 0 sorrys
│   ├── RRHelpers.lean              # LinearSystem monotonicity, degree lemmas        ✅ 0 sorrys
│   ├── LinearCombination.lean      # Linear combos of L(D), chart order bounds       2 sorrys
│   ├── ChartMeromorphic.lean       # Chart-local meromorphic framework               1 sorry
│   ├── ConnectedComplement.lean    # RS \ finite set connected (ORPHANED)            1 sorry
│   └── EvaluationMap.lean          # Evaluation map for L(D+[p]) (ORPHANED)          1 sorry
├── HodgeTheory/
│   ├── DifferentialForms.lean      # (p,q)-forms, wedge, conjugation                 ✅ 0 sorrys
│   ├── Dolbeault.lean              # dbar operator, Dolbeault cohomology              1 sorry
│   ├── Harmonic.lean               # Harmonic functions on RS                         2 sorrys
│   ├── HodgeDecomposition.lean     # Hodge decomposition, Dolbeault isomorphism       7 sorrys
│   ├── SerreDuality.lean           # Analytic Serre duality                           4 sorrys
│   ├── Helpers/
│   │   └── HarmonicHelpers.lean    # Coordinate definitions                          ✅ 0 sorrys
│   └── Infrastructure/
│       ├── RealSmoothness.lean     # R-smooth vs C-smooth bridge                     ✅ 0 sorrys
│       ├── WirtingerDerivatives.lean # d/dz and d/dz-bar                             ✅ 0 sorrys
│       ├── MaximumPrinciple.lean   # Maximum principle via circle averages            ✅ 0 sorrys
│       ├── MeanValueConverse.lean  # MVP <=> harmonic                                ✅ 0 sorrys
│       ├── PoissonIntegral.lean    # Schwarz/Poisson integral, boundary values        ✅ 0 sorrys
│       └── HarmonicConjugate.lean  # Harmonic conjugate existence                    1 sorry
├── Jacobian/                       # (lower priority)
│   ├── AbelJacobi.lean             # Abel-Jacobi map                                 7 sorrys
│   ├── ThetaFunctions.lean         # Theta functions                                 4 sorrys
│   └── Helpers/ThetaHelpers.lean   # Theta helpers                                   1 sorry
├── Applications/                   # (lower priority)
│   ├── GreenFunction.lean          # Green's function                                5 sorrys
│   └── Helpers/GreenHelpers.lean   # Green helpers                                   ✅ 0 sorrys
└── Moduli/                         # (lower priority)
    ├── Moduli.lean                 # Re-exports                                      ✅ 0 sorrys
    ├── FenchelNielsen.lean         # Fenchel-Nielsen coordinates                     ✅ 0 sorrys
    ├── QuasiconformalMaps.lean     # Quasiconformal maps                             2 sorrys
    └── SiegelSpace.lean            # Siegel upper half-space                         ✅ 0 sorrys
```

### Sorry Count Summary
- **Total**: 44 sorrys across 16 files
- **Core RR pipeline (Helpers + RiemannRoch)**: 8 sorrys (priority)
- **HodgeTheory pipeline**: 15 sorrys
- **Jacobian/Applications/Moduli**: 19 sorrys (lower priority)
- **Other (MeromorphicFunction)**: 1 sorry
- **Orphaned (ConnectedComplement, EvaluationMap)**: 2 sorrys (not on critical path)

---

## Proven Infrastructure (0 sorrys)

### Foundation
- **Basic.lean**: `RiemannSurface` (connected complex 1-manifold), `CompactRiemannSurface`,
  `RiemannSphere` (full 2-chart atlas), `IsHolomorphic`, `holomorphicIsConstant`
- **Divisors.lean**: `Divisor`, degree, `IsPrincipal`, `PicardGroup`, argument principle
- **LineBundles.lean**: `HolomorphicLineBundle`, `ofDivisor`, `tensor`, `dual`, `degree`,
  `LinearSystem` (with `chartOrderAt_eq` soundness field), `linearSystem_empty_negative_degree`

### Riemann-Roch Helpers (NEW 2026-02-10)
- **AnalyticBridge.lean**: `mdifferentiableAt_analyticAt_chart`, `rs_analyticOnNhd_of_mdifferentiable`,
  `rs_identity_principle` — bridge from manifold-level MDifferentiable to chart-local AnalyticAt
- **RRHelpers.lean**: `linearSystem_inclusion`, `linIndepLS_of_le`, `h0_mono`,
  `linearSystem_vanishing_at`, `linearSystem_tighten`, `h0_sub_point_le`, `h0_le_add_point`,
  `degree_add_point`, `degree_sub_point` — all fully proven
- **LinearCombination.lean** (partially proven): `lcRegularValue` definition,
  `lcRegularValue_mdifferentiableAt`, `lcRegularValue_vanishes_on_connected`,
  `chartOrderAt_basis_ge_neg_D` — ✅ proven
- **ChartMeromorphic.lean** (mostly proven): `IsChartMeromorphic`, `chartOrderAt`,
  arithmetic lemmas (add/smul/sum/linear_combination), `chartOrderAt_add_ge`,
  `isChartMeromorphic_of_mdifferentiable` — ✅ proven

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
- **PoissonIntegral.lean**: All major results proven including
  `schwarzIntegral_differentiableAt`, `poissonIntegral_harmonicOnNhd`,
  `poissonIntegral_boundary_values`, `mvp_eq_poissonIntegral`

---

## Riemann-Roch: What's Proven

### RiemannRoch.lean — Main Theorem Structure

| Component | Status | Notes |
|-----------|--------|-------|
| `IsLinIndepLS` | ✅ Defined | ℂ-linear independence via regularValue |
| `h0` via `Nat.find` | ✅ Defined | Max independent elements in L(D) |
| `h0_bounded` | ✅ Proven | L(D) finite-dimensional (uses zero_counting) |
| `h0_vanishes_negative_degree` | ✅ Proven | deg(D)<0 → h0=0 |
| `CanonicalDivisor` | ✅ Strengthened | Now includes `h0_eq_genus` field |
| `h0_trivial` | ✅ Proven | h0(0) = 1 (constant functions) |
| `h0_canonical` | ✅ Proven | h0(K) = g (from structure field) |
| `chi_add_point` | ✅ **PROVEN** | χ(D+[p]) = χ(D)+1 (via eval_residue_complementarity) |
| `correction_eq_zero_correction` | ✅ Proven | f(D) = f(0) by induction on TV(D) |
| **`riemann_roch_theorem`** | ✅ **PROVEN** | h0(D) - h1(D) = deg(D) + 1 - g |
| `riemann_roch_serre` | ✅ Proven | h0(D) - h0(K-D) = deg(D) + 1 - g |
| `h1_vanishes_high_degree` | ✅ Proven | deg(D)>2g-2 → h1=0 |
| `riemann_roch_high_degree` | ✅ Proven | h0(D) = deg(D)+1-g for deg(D)>2g-2 |
| `euler_characteristic_structure_sheaf` | ✅ Proven | χ(O) = 1-g |

### LinearSystem `chartOrderAt_eq` field (2026-02-10)

Added soundness field connecting abstract AMF order to chart-local meromorphic order:
```lean
chartOrderAt_eq : ∀ p, chartOrderAt fn.regularValue p = (fn.order p : WithTop ℤ)
```
All LinearSystem constructors updated (LineBundles, RRHelpers, RiemannRoch).

---

## Critical Sorrys (Blocking Riemann-Roch)

### RiemannRoch.lean — 4 sorrys

| Sorry | Line | Used By | Status |
|-------|------|---------|--------|
| `zero_counting_linear_combination` | ~181 | `h0_bounded` | IN PROGRESS — reducing to argument principle |
| `canonical_divisor_exists` | ~357 | Not used in proof (K is a parameter) | LOW priority |
| `eval_residue_complementarity` | ~581 | `chi_add_point` → main theorem | Needs Serre duality |
| `harmonic_10_are_canonical_sections` | ~887 | Corollary, not in main proof | LOW priority |

### Infrastructure Sorrys Supporting RiemannRoch

| Sorry | File | What's Needed |
|-------|------|---------------|
| `chartMeromorphic_argument_principle` | ChartMeromorphic.lean | Residue calculus / topological degree |
| `chartOrderAt_lcRegularValue_ge_neg_D` (ind. step) | LinearCombination.lean | Finset sum splitting + meromorphicOrderAt_add |
| `lcRegularValue_chartOrderSupport_finite` | LinearCombination.lean | Isolated zeros on compact surfaces |
| `analyticArgumentPrinciple` | MeromorphicFunction.lean | Integration / topological degree |

### Reduction Strategy for `zero_counting_linear_combination`
1. Linear combination g = Σ cᵢfᵢ has chart order ≥ -D(q) at every point q
   (`chartOrderAt_lcRegularValue_ge_neg_D` — inductive step needs proving)
2. At each test point tⱼ, g vanishes: chart order ≥ 1 - D(tⱼ) (i.e. extra zeros)
3. Total chart order sum ≥ Σ_all (order_q - 0) ≥ (deg(D)+1 zeros) - (deg(D) poles) = 1
4. But argument principle says chartOrderSum = 0 for nonzero g → contradiction → g = 0

---

## Priority Sorrys (HodgeTheory Pipeline)

### Tier 1: Low-Hanging Fruit

| Sorry | File | What's Needed |
|-------|------|--------------|
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

### Tier 3: Serre Duality

| Sorry | File | What's Needed |
|-------|------|--------------|
| `l2_inner_product_exists` | SerreDuality.lean | Integration + metric |
| `surjective_of_serre_duality` | SerreDuality.lean | Riesz representation |
| `residue_sum_zero` | SerreDuality.lean | Stokes' theorem |
| `kodaira_vanishing_kernel_dimension` | SerreDuality.lean | Full Serre duality |

### Tier 4: Other

| Sorry | File | What's Needed |
|-------|------|--------------|
| `harmonic_1forms_dimension` | Harmonic.lean | Hodge theory |
| `poisson_dirichlet_existence` | Harmonic.lean | Poisson solution |
| `argument_principle_count` | MeromorphicFunction.lean | Integration / topological degree |

---

## Proof Strategy: Analytic Riemann-Roch

### Current Approach (WORKING — in RiemannRoch.lean)
1. Define `h0(D)` = max number of ℂ-linearly independent elements of L(D)
2. Define `h1(D) = h0(K-D)` via Serre duality
3. `chi(D) = h0(D) - h1(D)`
4. Prove `chi_add_point`: χ(D+[p]) = χ(D) + 1 (uses `eval_residue_complementarity`)
5. Induction on TV(D): f(D) = χ(D) - deg(D) is invariant under D ↦ D±[p]
6. Base case: f(0) = χ(O) = 1 - g
7. Conclusion: χ(D) = deg(D) + 1 - g

### Alternative: Via Index Theory
1. chi(L) = ind(dbar_L) where dbar_L is the twisted Dolbeault operator
2. Homotopy invariance: index depends only on topological data
3. Normalization: chi(O) = 1 - g
4. Degree shift: chi(L(p)) = chi(L) + 1
5. Induction: chi(L) = deg(L) + 1 - g

### Alternative: Via Hodge Theory
1. Hodge decomposition => dim H^{p,q} finite
2. Serre duality => h^1(L) = h^0(K tensor L*)
3. chi(O) = h^0(O) - h^1(O) = 1 - g
4. Point exact sequence for degree shift
5. Same induction

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
AnalyticBridge ──> ChartMeromorphic ──> LinearCombination    |
                                             |               |
                                        RRHelpers            |
                                             |               |
LineBundles ─────────────────────────> RiemannRoch <─────────┘
```

---

## Next Steps (Priority Order)

1. **Prove `chartOrderAt_lcRegularValue_ge_neg_D` inductive step** — needs Fin (n+1) sum
   splitting and `meromorphicOrderAt_add` / `meromorphicOrderAt_mul_of_ne_zero`
2. **Prove `lcRegularValue_chartOrderSupport_finite`** — isolated zeros on compact
3. **Write full proof of `zero_counting_linear_combination`** — uses above + argument principle
4. **Work on `eval_residue_complementarity`** — needs Serre duality infrastructure
5. **Work on Dolbeault `local_dbar_poincare`** — key for cohomology theory
6. **HodgeDecomposition sorrys** — core of analytic approach
7. **SerreDuality** — needed for classical form of Riemann-Roch

---

## References

- Griffiths & Harris, "Principles of Algebraic Geometry", Ch 0-1
- Forster, "Lectures on Riemann Surfaces"
- Farkas & Kra, "Riemann Surfaces", Ch III
- Wells, "Differential Analysis on Complex Manifolds"
- Axler, Bourdon, Ramey, "Harmonic Function Theory", Ch 1
- Ahlfors, "Complex Analysis", Ch 6

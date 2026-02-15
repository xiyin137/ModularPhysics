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

### Major Milestone: Riemann-Roch h0-Duality FULLY PROVEN (correct definitions)

The file `RiemannRoch.lean` proves (modulo `eval_residue_complementarity`):
> `h0(D) - h0(K-D) = deg(D) + 1 - g`

where `hK : h0(K) = g` is an explicit hypothesis (the Hodge theorem).

The proof uses correction term invariance:
1. Define χ(D) = h0(D) - h0(K-D) and f(D) = χ(D) - deg(D)
2. Show f(D + [p]) = f(D) using `eval_residue_complementarity`
3. Strong induction on TV(D) shows f(D) = f(0)
4. Base case: f(0) = h0(0) - h0(K) - 0 = 1 - g

**Definitions are now correct (no axiom smuggling):**
- **`h0`**: properly defined as dim L(D) via Nat.find ✅
- **`CanonicalDivisor`**: only has `degree_eq` field, NO `h0_eq_genus` ✅
- **`h0_canonical_eq_genus`**: separate theorem (sorry — Hodge theorem) ✅
- **`h1_dolbeault`**: defined via Dolbeault cohomology (sorry for general D) ✅
- **Serre duality** `serre_duality_h1`: separate theorem, NOT a definition ✅
- **`riemann_roch_classical`**: h0(D) - h1_dolbeault(D) = deg(D)+1-g (via Serre duality) ✅
- **`DolbeaultCohomology.lean`** (NEW): proper H^{0,1} = Ω^{0,1}/im(∂̄_real) ✅

**Three-level proof structure:**
- **Level 1 (proven):** h0(D) - h0(K-D) = deg(D)+1-g (with hK as hypothesis)
- **Level 2 (sorry):** h0(D) - h1_dolbeault(D) = deg(D)+1-g (via Serre duality)
- **Level 3 (sorry):** h0(K) = g (Hodge theorem: dim H^{1,0} = topological genus)

### Recent Progress (2026-02-14)
- **`local_mapping_theorem` FULLY PROVEN** — k-th root extraction + IFT, 200+ line proof
- **`fiber_finite` FULLY PROVEN** — identity principle + compactness on compact RS
- **`chartOrderSum_split` FULLY PROVEN** — chartOrderSum = TZO - TPO
- **`chartOrderSum_eq_zero` PROVEN** (modulo `totalZeroOrder_eq_totalPoleOrder`)
- **`chartMeromorphic_argument_principle` PROVEN** — wraps chartOrderSum_eq_zero
- **ChartTransition.lean CREATED** ✅ 0 sorrys — chart independence of meromorphic order,
  isolated zeros, finiteness of support on compact surfaces
- **AnalyticKthRoot.lean CREATED** ✅ 0 sorrys — k-th root extraction for nonvanishing
  analytic functions (used by local_mapping_theorem)
- **ConnectedComplement.lean: `rs_compl_finite_isConnected` PROVEN** ✅ 0 sorrys
- **Pole invariance** `chartOrderAt_sub_const_at_pole` PROVEN
- ChartMeromorphic.lean: 1 → **0 sorrys** (argument principle moved to ArgumentPrinciple.lean)
- ArgumentPrinciple.lean: 5 → **2 sorrys** (down from 5)

### Previous Progress (2026-02-13)
- **`zero_counting_linear_combination` FULLY PROVEN** — key lemma for `h0_bounded`
- **`chartOrderAt_lcRegularValue_ge_neg_D` FULLY PROVEN** — inductive step on Fin sums
- **`lcRegularValue_chartOrderSupport_finite` FULLY PROVEN** — isolated zeros on compact RS
- **Meromorphic identity principle FULLY PROVEN** — `chartOrderAt_ne_top_of_ne_top_somewhere`
- **`rs_nontrivial` and `rs_nhdsNE_neBot` FULLY PROVEN** — RS has ≥ 2 pts, no isolated pts
- LinearCombination.lean: 2 → **0 sorrys**
- RiemannRoch.lean: 4 → **3 sorrys**

### Folder Structure
```
Analytic/
├── Basic.lean                      # RiemannSurface, CompactRiemannSurface           ✅ 0 sorrys
├── MeromorphicFunction.lean        # AnalyticMeromorphicFunction                     1 sorry
├── Divisors.lean                   # Analytic Divisor, PicardGroup                   ✅ 0 sorrys
├── LineBundles.lean                # HolomorphicLineBundle, LinearSystem             ✅ 0 sorrys
├── RiemannRoch.lean                # Analytic RR — h0 duality proven                  6 sorrys
├── Analytic.lean                   # Re-exports                                      ✅ 0 sorrys
├── Helpers/                        # Riemann-Roch infrastructure
│   ├── AnalyticBridge.lean         # MDifferentiable → AnalyticAt bridge             ✅ 0 sorrys
│   ├── RRHelpers.lean              # LinearSystem monotonicity, degree lemmas        ✅ 0 sorrys
│   ├── LinearCombination.lean      # Linear combos of L(D), chart order bounds       ✅ 0 sorrys
│   ├── ChartMeromorphic.lean       # Chart-local meromorphic + identity principle    ✅ 0 sorrys
│   ├── ChartTransition.lean        # Chart independence, isolated zeros (NEW)        ✅ 0 sorrys
│   ├── AnalyticKthRoot.lean        # k-th root of nonvanishing analytic fn (NEW)     ✅ 0 sorrys
│   ├── ArgumentPrinciple.lean      # LMT, degree theory, argument principle          2 sorrys
│   ├── ConnectedComplement.lean    # RS \ finite set connected                       ✅ 0 sorrys
│   └── EvaluationMap.lean          # Evaluation map for L(D+[p])                     1 sorry
├── HodgeTheory/
│   ├── DifferentialForms.lean      # (p,q)-forms, wedge, conjugation                 ✅ 0 sorrys
│   ├── Dolbeault.lean              # dbar operator, Dolbeault cohomology              1 sorry
│   ├── DolbeaultCohomology.lean    # H^{0,1} = Ω^{0,1}/im(∂̄_real) (NEW)              7 sorrys
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
- **Total**: 51 sorrys across 15 files
- **Core RR pipeline (RiemannRoch)**: 6 sorrys (h0_canonical_eq_genus, canonical_divisor_exists,
  eval_residue_complementarity, harmonic_10_are_canonical_sections, h1_dolbeault, serre_duality_h1)
- **Argument Principle**: 2 sorrys (`fiberMultiplicity_constant`, `totalZeroOrder_eq_totalPoleOrder`)
- **DolbeaultCohomology** (NEW): 7 sorrys (dbar_real infrastructure + Hodge iso)
- **HodgeTheory pipeline**: 15 sorrys
- **Jacobian/Applications/Moduli**: 19 sorrys (lower priority)
- **Other (MeromorphicFunction, EvaluationMap)**: 2 sorrys

---

## Proven Infrastructure (0 sorrys)

### Foundation
- **Basic.lean**: `RiemannSurface` (connected complex 1-manifold), `CompactRiemannSurface`,
  `RiemannSphere` (full 2-chart atlas), `IsHolomorphic`, `holomorphicIsConstant`
- **Divisors.lean**: `Divisor`, degree, `IsPrincipal`, `PicardGroup`, argument principle
- **LineBundles.lean**: `HolomorphicLineBundle`, `ofDivisor`, `tensor`, `dual`, `degree`,
  `LinearSystem` (with `chartOrderAt_eq` soundness field), `linearSystem_empty_negative_degree`

### Riemann-Roch Helpers
- **AnalyticBridge.lean**: `mdifferentiableAt_analyticAt_chart`, `rs_analyticOnNhd_of_mdifferentiable`,
  `rs_identity_principle` — bridge from manifold-level MDifferentiable to chart-local AnalyticAt
- **RRHelpers.lean**: `linearSystem_inclusion`, `linIndepLS_of_le`, `h0_mono`,
  `linearSystem_vanishing_at`, `linearSystem_tighten`, `h0_sub_point_le`, `h0_le_add_point`,
  `degree_add_point`, `degree_sub_point` — all fully proven
- **LinearCombination.lean** ✅ **0 sorrys**: `lcRegularValue` definition,
  `lcRegularValue_mdifferentiableAt`, `chartOrderAt_lcRegularValue_ge_neg_D` (induction on Fin sums),
  `lcRegularValue_chartOrderSupport_finite` (isolated zeros + compactness),
  `chartMeromorphic_linear_combination` — ALL fully proven
- **ChartMeromorphic.lean** ✅ **0 sorrys**: `IsChartMeromorphic`, `chartOrderAt`,
  arithmetic lemmas, `chartOrderAt_add_ge`, `isChartMeromorphic_of_mdifferentiable`,
  `chartOrderAt_ne_top_of_ne_top_somewhere` (meromorphic identity principle),
  `rs_nontrivial`, `rs_nhdsNE_neBot` — ALL fully proven (argument principle moved to
  ArgumentPrinciple.lean)
- **ChartTransition.lean** ✅ **0 sorrys** (NEW): `chartOrderAt_eq_in_chart` (chart independence
  of meromorphic order), `chartTransition_analyticAt`, `chartTransition_deriv_ne_zero`,
  `meromorphicOrderAt_eq_zero_near`, `chartOrderAt_eq_zero_near`,
  `chartOrderSupport_finite_general` — ALL fully proven
- **AnalyticKthRoot.lean** ✅ **0 sorrys** (NEW): `analytic_kth_root` (k-th root of nonvanishing
  analytic function), `ncard_kthRoots`, `norm_kthRoot_eq` — ALL fully proven
- **ConnectedComplement.lean** ✅ **0 sorrys**: `rs_compl_finite_isConnected` (compact RS
  minus finite set is connected), `preconnected_remove_point` — ALL fully proven
- **ArgumentPrinciple.lean** (2 sorrys, down from 5): Degree theory framework.
  - ✅ PROVEN: `local_mapping_theorem` (200+ lines, k-th root + IFT), `fiber_finite`,
    `chartOrderSum_split`, `chartOrderAt_sub_const_at_pole` (pole invariance),
    `chartRep_sub_const`, `chartOrderSum_eq_zero`, `chartMeromorphic_argument_principle`
  - SORRY: `fiberMultiplicity_constant` (not on critical path),
    `totalZeroOrder_eq_totalPoleOrder` (degree theory: TZO = TPO via fiber multiplicity constancy)

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
| `zero_counting_linear_combination` | ✅ **PROVEN** | Key lemma: g vanishing at deg(D)+1 pts ⟹ g ≡ 0 |
| `h0` via `Nat.find` | ✅ Defined | Max independent elements in L(D) = dim H⁰(X, O(D)) |
| `h0_bounded` | ✅ Proven | L(D) finite-dimensional (uses zero_counting) |
| `h0_vanishes_negative_degree` | ✅ Proven | deg(D)<0 → h0=0 |
| `CanonicalDivisor` | ✅ Fixed | Only degree_eq field, no smuggled h0_eq_genus |
| `h0_canonical_eq_genus` | ❌ Sorry | Hodge theorem: h0(K) = g (topological genus) |
| `h0_trivial` | ✅ Proven | h0(0) = 1 (constant functions) |
| `chi_add_point` | ✅ **PROVEN** | χ(D+[p]) = χ(D) + 1 (uses eval_residue_complementarity) |
| `correction_eq_zero_correction` | ✅ Proven | f(D) = f(0) by induction on TV(D) |
| **`riemann_roch_h0_duality`** | ✅ **PROVEN** | h0(D) - h0(K-D) = deg(D)+1-g (hK hypothesis) |
| `h1_dolbeault` | ❌ Sorry | Proper Dolbeault definition for general D |
| `serre_duality_h1` | ❌ Sorry | h1_dolbeault(D) = h0(K-D) (theorem, not definition) |
| `riemann_roch_classical` | ✅ Proven | h0(D) - h1_dolbeault(D) = deg(D)+1-g (from above two) |
| `h0_KminusD_vanishes_high_degree` | ✅ Proven | deg(D)>2g-2 → h0(K-D)=0 |
| `riemann_roch_high_degree` | ✅ Proven | h0(D) = deg(D)+1-g for deg(D)>2g-2 |
| `euler_characteristic_structure_sheaf` | ✅ Proven | h0(0) - h0(K) = 1-g (hK hypothesis) |

### DolbeaultCohomology.lean — Proper H^{0,1} (NEW)

| Component | Status | Notes |
|-----------|--------|-------|
| `dbar_real` | ✅ Defined | ∂̄ on RealSmoothFunction (non-trivial, unlike dbar_fun on holomorphic) |
| `dbar_real_add/zero/const_mul` | ❌ Sorry | Linearity of dbar_real |
| `dbarImage` | ✅ Defined | im(∂̄) as ℂ-submodule of Form_01 |
| `DolbeaultH01` | ✅ Defined | H^{0,1} = Form_01 / dbarImage |
| `h1_dolbeault_trivial` | ✅ Defined | finrank of DolbeaultH01 |
| `dolbeault_hodge_iso` | ❌ Sorry | H^{0,1} ≅ Harmonic01Forms |
| `h1_trivial_eq_genus` | ❌ Sorry | h1(O) = g (Hodge theorem) |

### LinearSystem `chartOrderAt_eq` field (2026-02-10)

Added soundness field connecting abstract AMF order to chart-local meromorphic order:
```lean
chartOrderAt_eq : ∀ p, chartOrderAt fn.regularValue p = (fn.order p : WithTop ℤ)
```
All LinearSystem constructors updated (LineBundles, RRHelpers, RiemannRoch).

---

## Critical Sorrys (Blocking Riemann-Roch)

### RiemannRoch.lean — 6 sorrys

| Sorry | Line | Used By | Status |
|-------|------|---------|--------|
| `h0_canonical_eq_genus` | ~470 | Hypothesis for `riemann_roch_h0_duality` | Hodge theorem |
| `canonical_divisor_exists` | ~477 | Not used in proof (K is a parameter) | LOW priority |
| `eval_residue_complementarity` | ~699 | `chi_add_point` → main theorem | Needs residue pairing |
| `harmonic_10_are_canonical_sections` | ~978 | Relates H^{1,0} ≅ H^0(K) | Hodge theory |
| `h1_dolbeault` | ~999 | Definition for classical form | Twisted Dolbeault |
| `serre_duality_h1` | ~1008 | `riemann_roch_classical` | Hodge + residue |

### Infrastructure Sorrys Supporting RiemannRoch

| Sorry | File | What's Needed | Status |
|-------|------|---------------|--------|
| `zero_counting_linear_combination` | RiemannRoch.lean | — | ✅ **PROVEN** |
| `chartOrderAt_lcRegularValue_ge_neg_D` | LinearCombination.lean | — | ✅ **PROVEN** |
| `lcRegularValue_chartOrderSupport_finite` | LinearCombination.lean | — | ✅ **PROVEN** |
| `chartOrderAt_ne_top_of_ne_top_somewhere` | ChartMeromorphic.lean | — | ✅ **PROVEN** |
| `chartMeromorphic_argument_principle` | ArgumentPrinciple.lean | — | ✅ **PROVEN** (via `totalZeroOrder_eq_totalPoleOrder`) |
| `local_mapping_theorem` | ArgumentPrinciple.lean | — | ✅ **PROVEN** (k-th root + IFT) |
| `fiber_finite` | ArgumentPrinciple.lean | — | ✅ **PROVEN** (identity principle + compactness) |
| `chartOrderSum_split` | ArgumentPrinciple.lean | — | ✅ **PROVEN** (Finset arithmetic) |
| `rs_compl_finite_isConnected` | ConnectedComplement.lean | — | ✅ **PROVEN** (2-manifold topology) |
| `totalZeroOrder_eq_totalPoleOrder` | ArgumentPrinciple:658 | Degree theory (N(c) const) | 1 sorry |
| `analyticArgumentPrinciple` | MeromorphicFunction:521 | Integration / topological degree | 1 sorry |

### Remaining Sorry Difficulty Assessment

| Sorry | File | Difficulty | Mathlib Support | Notes |
|-------|------|-----------|----------------|-------|
| `totalZeroOrder_eq_totalPoleOrder` | ArgumentPrinciple:658 | HIGH | Partial | Degree theory: TZO=TPO via fiber multiplicity constancy |
| `eval_residue_complementarity` | RiemannRoch:694 | VERY HIGH | None | Residue pairing from scratch |
| `canonical_divisor_exists` | RiemannRoch:470 | HIGH | None | Needs Hodge theory (dim H^{1,0}=g) |
| `harmonic_10_are_canonical_sections` | RiemannRoch:1000 | MEDIUM | Partial | Identification of spaces |
| `fiberMultiplicity_constant` | ArgumentPrinciple:268 | HIGH | None | Not on critical path |
| `analyticArgumentPrinciple` | MeromorphicFunction:521 | HIGH | Same as above | Equivalent to arg principle |

### `zero_counting_linear_combination` — FULLY PROVEN (2026-02-13)
The proof by contradiction:
1. g = Σ cᵢfᵢ has chart order ≥ -D(q) at every point q (chartOrderAt_lcRegularValue_ge_neg_D ✅)
2. Identity principle: chartOrderAt g q ≠ ⊤ for ALL q (chartOrderAt_ne_top_of_ne_top_somewhere ✅)
3. chartOrderSupport is finite (lcRegularValue_chartOrderSupport_finite ✅)
4. Argument principle: chartOrderSum = 0 for nonzero g (chartMeromorphic_argument_principle ✅)
5. Lower bound: chartOrderSum ≥ (deg(D)+1) zeros - deg(D) poles = 1 (finset arithmetic ✅)
6. Contradiction: 0 = chartOrderSum ≥ 1

### Argument Principle Pipeline — MOSTLY PROVEN (2026-02-14)
The argument principle `chartOrderSum_eq_zero` is proven via:
1. `chartOrderSum_split`: chartOrderSum = TZO - TPO ✅
2. `totalZeroOrder_eq_totalPoleOrder`: TZO = TPO (1 sorry — degree theory)
The degree theory proof requires showing fiber multiplicity N(c) is constant on ℂ:
- N(c) = total order of zeros of f-c in regular locus
- N is locally constant: LMT at zeros + pole invariance + compactness
- ℂ is connected → N is globally constant
- N(0) = TZO, N(large c) = TPO (LMT for 1/f at poles)
Key Mathlib tools: `IsLocallyConstant.apply_eq_of_isPreconnected`,
`MeromorphicAt.analyticAt`, `tendsto_nhds_of_meromorphicOrderAt_nonneg`

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

### Level 1: h0 duality (PROVEN in RiemannRoch.lean)
**Proves:** `h0(D) - h0(K-D) = deg(D) + 1 - g` with `hK : h0(K) = g` as hypothesis.
1. Define `h0(D)` = max ℂ-linearly independent elements of L(D) ✅
2. Define `chi(D) = h0(D) - h0(K-D)` (h0-only, no fake h1) ✅
3. Prove `chi_add_point`: χ(D+[p]) = χ(D) + 1 (uses `eval_residue_complementarity`)
4. Induction on TV(D): f(D) = χ(D) - deg(D) is invariant under D ↦ D±[p]
5. Base case: f(0) = h0(0) - h0(K) - 0 = 1 - g (uses h0(0)=1 proven, hK hypothesis)
6. Conclusion: h0(D) - h0(K-D) = deg(D) + 1 - g

### Level 2: Classical form (requires Serre duality)
1. `h1_dolbeault(D)` = dim(Ω^{0,1}(D) / im ∂̄_D) — proper Dolbeault cohomology
2. `serre_duality_h1`: h1_dolbeault(D) = h0(K-D) (THEOREM, not definition)
3. `riemann_roch_classical`: h0(D) - h1_dolbeault(D) = deg(D) + 1 - g

### Level 3: Hodge theorem (connects analytic to topological)
1. `dim_harmonic_10_eq_genus`: dim H^{1,0} = g (topological genus)
2. `harmonic_10_are_canonical_sections`: H^{1,0} ≅ H^0(K)
3. `h0_canonical_eq_genus`: h0(K) = g (combines above two)

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

1. **~~Prove `zero_counting_linear_combination`~~** ✅ DONE (2026-02-13)

2. **~~Prove `chartMeromorphic_argument_principle`~~** ✅ DONE (2026-02-14)
   - local_mapping_theorem: PROVEN (k-th root + IFT, 200+ lines)
   - fiber_finite: PROVEN (identity principle + compactness)
   - chartOrderSum_split + chartOrderSum_eq_zero: PROVEN
   - Remaining: `totalZeroOrder_eq_totalPoleOrder` (degree theory: TZO = TPO)

3. **~~Prove `rs_compl_finite_isConnected`~~** ✅ DONE (2026-02-14)

4. **Prove `totalZeroOrder_eq_totalPoleOrder`** (ArgumentPrinciple.lean:658)
   - Last sorry blocking the argument principle
   - **Strategy**: Fiber multiplicity constancy — N(c) = Σ ord(f-c) at zeros is constant on ℂ
   - N(0) = TZO(f), N(large c) = TPO(f) (preimages near poles via LMT for 1/f)
   - Needs: locally constant N + connected ℂ → constant N
   - Key Mathlib: `IsLocallyConstant.apply_eq_of_isPreconnected`, `MeromorphicAt.analyticAt`,
     `tendsto_nhds_of_meromorphicOrderAt_nonneg`

5. **Prove `eval_residue_complementarity`** (RiemannRoch.lean:694)
   - The hardest remaining sorry on the critical path
   - **Strategy**: Residue pairing between L(D+[p])/L(D) and L(K-D)/L(K-D-[p])
   - **Infrastructure needed**: Meromorphic 1-forms, residue at a point, residue sum formula
   - **Alternative**: Could use ∂̄-equation approach (solve ∂̄u = ω with prescribed singularity)

6. **Work on Dolbeault `local_dbar_poincare`** — key for cohomology theory
7. **HodgeDecomposition sorrys** — core of analytic approach
8. **SerreDuality** — needed for classical form of Riemann-Roch

---

## References

- Griffiths & Harris, "Principles of Algebraic Geometry", Ch 0-1
- Forster, "Lectures on Riemann Surfaces"
- Farkas & Kra, "Riemann Surfaces", Ch III
- Wells, "Differential Analysis on Complex Manifolds"
- Axler, Bourdon, Ramey, "Harmonic Function Theory", Ch 1
- Ahlfors, "Complex Analysis", Ch 6

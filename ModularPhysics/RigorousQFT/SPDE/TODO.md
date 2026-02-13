# SPDE Standard Approach - Status and TODO

## Current Sorry Count (as of 2026-02-13)

| File | Sorrys | Key Items |
|------|--------|-----------|
| **StochasticIntegration.lean** | **9** | ito_formula(martingale), quadratic_variation, bdg_inequality, sde_existence, sde_uniqueness_law, stratonovich, semimartingale_integral, girsanov, martingale_representation |
| **BrownianMotion.lean** | **6** | time_inversion, eval_unit_is_brownian, Q-Wiener continuous_paths, Q-Wiener regularity_from_trace, levy_characterization, (t<0 design) |
| **SPDE.lean** | **6** | Generator/semigroup infrastructure (renormalized_spde nontriviality FIXED) |
| **Basic.lean** | **1** | is_martingale_of_bounded (needs uniform integrability) |
| **RegularityStructures.lean** | **1** | Abstract approach (complementary to folder) |
| **Probability/Basic.lean** | **2** | condexp_jensen, doob_maximal_L2 |
| **Probability/IndependenceHelpers.lean** | **0** | Fully proven |
| **Helpers/InnerIntegralIntegrability.lean** | **3** | Tonelli/Fubini infrastructure |
| **Helpers/ItoFormulaProof.lean** | **2** | ito_lower_order_L2_convergence, ito_formula_martingale (1 L2 conv at t') |
| **Helpers/ItoFormulaDecomposition.lean** | **1** | taylor_remainder_L2_convergence (Fatou structure in place, needs QV infra) |
| **Helpers/QuadraticVariation.lean** | **4** | QV bound, QV sq integrable, discrete QV L² conv, Taylor remainders a.e. |
| **Helpers/QuarticBound.lean** | **3** | L4 transfer sorrys |
| **Helpers/** (all other) | **0** | 13 files, all fully proven |
| **RegularityStructures/** | **44** | See RegularityStructures/TODO.md |

**Total: 82 sorrys** (38 SPDE core + 44 RegularityStructures)

---

## Soundness Audit (2026-02-12)

**All files audited for definition soundness and axiom smuggling.**

### Results:
- **StochasticIntegration.lean**: ✓ SOUND — all structures properly defined
- **BrownianMotion.lean**: ✓ SOUND — all structures properly defined
- **Basic.lean**: ✓ SOUND — Filtration, Martingale, LocalMartingale all correct
- **SPDE.lean**: ✓ SOUND (after fix) — `PolynomialNonlinearity.leading_nonzero` replaces weak `nontrivial`
- **Probability/Basic.lean**: ✓ SOUND — `IsGaussian` correctly includes char_function as defining property
- **Helpers/**: ✓ SOUND — 15 files, no issues
- **No axioms, no .choose in definitions, no True := trivial**

### Fix applied:
- `PolynomialNonlinearity`: replaced `nontrivial : ∃ k, coeff k ≠ 0` with
  `leading_nonzero : coeff ⟨degree, ...⟩ ≠ 0` (proper polynomial of stated degree)
- This eliminated the `sorry` in `renormalized_spde` (leading coeff unchanged by renormalization)
- Old `nontrivial` is now a derived lemma

---

## Reconstruction Theorem — USES SORRY (3 blocking)

`reconstruction_theorem` in `Reconstruction.lean` has a proof term but
**transitively depends on 3 sorry'd lemmas** in the uniqueness argument.
See `RegularityStructures/TODO.md` for full sorry-dependency audit.

**What is proven:**
- `reconstruction_exists` — FULLY PROVEN (explicit construction R(f) = Π_x f(x))
- `extendModelPairing_bound` — FULLY PROVEN
- `reconstruction_pairing_diff_bound` — FULLY PROVEN

**Blocking sorrys (3):**
1. `pairing_eq_of_small_scale_bound` (Reconstruction.lean:399) — Prop 3.19, requires Littlewood-Paley
2. `pairing_eq_of_small_scale_eq` scale > 1 (Reconstruction.lean:427) — scale extension
3. `pairing_eq_of_small_scale_eq` scale ≤ 0 (Reconstruction.lean:430) — domain boundary

**RegularityStructures sorry breakdown:**
- Trees/ — 0 sorrys (fully proven)
- Models/Admissible.lean — 0 sorrys (fully proven)
- Reconstruction.lean — 5 sorrys (3 blocking + 2 corollaries)
- Models/Canonical.lean — 15 sorrys (specific model, not blocking reconstruction)
- FixedPoint.lean — 10 sorrys (downstream application)
- BPHZ.lean — 11 sorrys (downstream renormalization)
- BesovCharacterization.lean — 2 sorrys
- SmoothCutoff.lean — 1 sorry

---

## Itô Formula Roadmap (Current Priority)

**Goal:** Prove `ito_formula` martingale property (part ii) in StochasticIntegration.lean

**Current status:**
- Parts (i) initial condition and (iii) formula: PROVED
- Part (ii) martingale property: **SORRY** — the sole non-trivial content
- **ItoProcess definition updated**: added `process_continuous` field (a.s. continuous paths)
- **Approach switched from C3 to C2** (standard approach, more general)
- **Deprecated**: 5th/6th moment infrastructure + TaylorBound.lean moved to /backup_deprecated/

**Statement:**
For C² function f and Itô process dX_t = μ_t dt + σ_t dW_t:
```
f(t, X_t) = f(0, X_0) + ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds + M_t
```
where M_t is a martingale (the stochastic integral ∫₀ᵗ ∂_x f · σ dW).

**Dependency chain (→ = depends on):**
```
ito_formula (StochasticIntegration.lean, line 1651)
  → ito_formula_martingale (ItoFormulaProof.lean)
    → ito_integral_martingale_setIntegral ✅ PROVEN
    → ito_formula_L2_convergence (ItoFormulaProof.lean)
      → ito_weighted_qv_convergence ✅ PROVEN
      → ito_lower_order_L2_convergence ❌ SORRY (MAIN BLOCKER)
      → 3 internal sorrys: integrability (×2) + integral splitting
    → 1 sorry: L² conv application at time t'
```

**Proof infrastructure status:**

| Component | Status | Location |
|-----------|--------|----------|
| `itoRemainder` definition | ✅ DONE | ItoFormulaProof.lean |
| `taylor_second_order_bound` | ✅ DONE | ItoFormulaProof.lean |
| `contDiff_two_deriv_continuous` | ✅ DONE | ItoFormulaProof.lean |
| `partitionTime` + arithmetic | ✅ DONE | ItoFormulaProof.lean |
| `itoPartitionProcess` construction | ✅ DONE | ItoFormulaProof.lean |
| `itoPartitionProcess_adapted` | ✅ DONE | ItoFormulaProof.lean |
| `itoPartitionProcess_bounded` | ✅ DONE | ItoFormulaProof.lean |
| `itoPartitionProcess_times_nonneg` | ✅ DONE | ItoFormulaProof.lean |
| `ito_formula_martingale` (structure) | ✅ DONE (1 sorry) | ItoFormulaProof.lean |
| `bm_qv_sum_L2_bound` | ✅ DONE | ItoFormulaInfrastructure.lean |
| `bm_qv_L2_convergence` | ✅ DONE | ItoFormulaInfrastructure.lean |
| `weighted_qv_sum_L2_bound` | ✅ DONE | ItoFormulaInfrastructure.lean |
| `weighted_qv_L2_convergence` | ✅ DONE | ItoFormulaInfrastructure.lean |
| `stochasticIntegral_at_sq_integrable` | ✅ DONE | ItoFormulaDecomposition.lean |
| `stochasticIntegral_at_filtration_measurable` | ✅ DONE | ItoFormulaDecomposition.lean |
| `integral_mul_eq_zero_of_setIntegral_eq_zero` | ✅ DONE | ItoFormulaDecomposition.lean |
| `simple_bilinear_isometry_different_times` | ✅ DONE | ItoFormulaDecomposition.lean |
| `simple_increment_L2` | ✅ DONE | ItoFormulaDecomposition.lean |
| **`ito_formula_L2_convergence`** | **3 sorrys** | ItoFormulaProof.lean |
| **`ito_lower_order_L2_convergence`** | **SORRY** | ItoFormulaProof.lean |

**Blocking sorrys for the Itô formula (by priority):**

1. **`ito_lower_order_L2_convergence`** — MAIN BLOCKER. Shows Taylor remainders + Riemann sum errors + cross terms → 0 in L². With C2 approach:
   - Taylor remainder: uses Fatou + modulus of continuity of f'', only needs 4th moments
   - Riemann sums: Σ g(tᵢ)Δt → ∫ g ds for bounded adapted g
   - Cross terms: E[(Δt·ΔW)], E[(ΔSI - σΔW)²] → 0

2. **1 sorry in `ito_formula_martingale`** — Application of L2 convergence at time t'. Becomes trivial once lower_order is proved.

**Supporting infrastructure still needed (in ItoFormulaDecomposition.lean):**

| Component | Status | Purpose |
|-----------|--------|---------|
| `stoch_integral_increment_L2_bound` | SORRY | E[|SI(t)-SI(s)|²] ≤ Mσ²(t-s) |
| `ito_process_increment_L2_bound` | SORRY | E[|X(t)-X(s)|²] ≤ C(t-s) |
| `ito_process_increment_L4_bound` | PROVEN | E[|X(t)-X(s)|⁴] ≤ C(t-s)², key for C2 approach |
| `riemann_sum_L2_convergence` | SORRY | Σ g(tᵢ)Δt → ∫ g ds in L² |
| `taylor_remainder_L2_convergence` | REWRITE NEEDED | C2 Fatou approach (replacing C3 6th moment) |

**Key infrastructure already available:**
- `ito_integral_martingale_setIntegral` — martingale from L² limits ✅
- `taylor_mean_remainder_bound` — Taylor with ‖remainder‖ bound ✅
- BM increments: `increment_variance`, `increment_mean_zero`, `increment_fourth_moment` ✅
- `increment_sq_minus_dt_variance` — Var((ΔW)²-Δt) = 2(Δt)² ✅
- `cross_term_zero` — simple process cross-term vanishing ✅
- `integral_mul_zero_of_indep_zero_mean` — E[X·Y]=0 for adapted×independent ✅
- `integral_mul_eq_zero_of_setIntegral_eq_zero` — martingale orthogonality ✅
- `simple_bilinear_isometry_different_times` — E[S(t)S(s)] = E[S(s)²] ✅

**Priority ordering:**
1. Itô formula via direct partition approach (solve blocking sorrys above)
2. `quadratic_variation` as corollary (apply Itô to f(x) = x²)
3. `sde_uniqueness_law` via Grönwall (infrastructure in Helpers/GronwallForSDE.lean)

---

## Other Sorrys by File

### StochasticIntegration.lean (9 sorrys)
1. `bdg_inequality` (line 1322) — Burkholder-Davis-Gundy inequality
2. `quadratic_variation` (line 1474) — QV of Itô process
3. `ito_formula` martingale property (line 1651) — **CURRENT PRIORITY**
4. `sde_existence_uniqueness` (line 1692) — SDE existence via Picard iteration
5. `sde_uniqueness_law` (line 1731) — Pathwise uniqueness via Grönwall
6. `stratonovich_chain_rule` (line 1766) — Stratonovich chain rule
7. `semimartingale_integral_exists` (line 1915) — Semimartingale integral construction
8. `girsanov` (line 1945) — Girsanov theorem
9. `martingale_representation` (line 1971) — Martingale representation theorem

### BrownianMotion.lean (6 sorrys)
1. t < 0 case (line 212) — Design choice for ℝ-indexed BM
2. `time_inversion` (line 595) — t·W(1/t) is BM
3. `eval_unit_is_brownian` (line 648) — Cylindrical Wiener unit evaluation
4. `continuous_paths` (line 744) — Q-Wiener continuous paths
5. `regularity_from_trace` (line 749) — Q-Wiener regularity
6. `levy_characterization` (line 782) — Lévy characterization

### Helpers/InnerIntegralIntegrability.lean (3 sorrys)
1. `inner_sq_integral_integrable_of_sub_interval` a.e. bound (line 82)
2. `inner_product_integral_integrable` a.e. bound (line 100)
3. `integrableOn_ae_of_square_integrable` (line 115)

---

## Fully Proven Components

### Helpers/ (13 files, 0 sorrys + 2 files with sorrys)
- **CommonRefinement.lean** — Merged partitions, valueAtTime, joint measurability
- **SimpleProcessLinear.lean** — Linear combination of simple process integrals
- **MergedValueAtTime.lean** — valueAtTime linearity for merged processes
- **SimpleIntegralMartingale.lean** — Simple stochastic integral is martingale
- **SetIntegralHelpers.lean** — Cross-term vanishing, variance factorization on sets
- **L2LimitInfrastructure.lean** — Set integral convergence from L² convergence
- **ItoIntegralProperties.lean** — Itô isometry proof, martingale proof
- **IsometryAt.lean** — isometry_at, bilinear_isometry_at
- **ProductL2Convergence.lean** — Product L² convergence
- **IteratedProductConvergence.lean** — Iterated integral product convergence
- **SimpleProcessDef.lean** — SimpleProcess structure, stochasticIntegral definitions
- **GronwallForSDE.lean** — Grönwall lemma infrastructure
- **ItoFormulaInfrastructure.lean** — BM QV L² convergence, weighted QV convergence

### Probability/ (2 files, 0 sorrys)
- **IndependenceHelpers.lean** — Bridge lemmas for independence
- **Pythagoras.lean** — L² Pythagoras for orthogonal RVs

### RegularityStructures/Trees/ (3 files, 0 sorrys)
- **Basic.lean** — MultiIndex, TreeSymbol, complexity
- **Homogeneity.lean** — homogeneity_decomposition, FormalSum algebra
- **Operations.lean** — Standard trees for Φ⁴/KPZ

### Key Proven Theorems
- **Itô isometry** (simple + L² limit): `E[(∫H dW)²] = E[∫H² ds]`
- **Bilinear Itô isometry**: `E[(∫H₁ dW)(∫H₂ dW)] = E[∫H₁H₂ ds]`
- **Itô integral is martingale**: set-integral property on [0,T]
- **Itô integral linearity**: `I(aH₁ + bH₂) = aI(H₁) + bI(H₂)` in L²
- **BM quadratic variation compensator**: W²_t - t is martingale
- **BM quadratic variation L² convergence**: E[|Σ(ΔW)²-t|²] → 0
- **Weighted QV convergence**: Σ gᵢ[(ΔWᵢ)²-Δtᵢ] → 0 in L² for adapted bounded g
- **Martingale orthogonality**: ∫_A Y=0 ∀A∈F_s, X is F_s-meas → E[X·Y]=0 (via condExp)
- **Bilinear isometry at different times**: E[S(t)·S(s)] = E[S(s)²] for s≤t
- **Simple process increment L²**: E[|S(t)-S(s)|²] = E[S(t)²]-E[S(s)²]
- **BM scaling**: c^{-1/2}W_{ct} is BM
- **BM reflection**: -W is BM
- **Reconstruction exists**: explicit construction R(f) = Π_x f(x)

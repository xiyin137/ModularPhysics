# SPDE Standard Approach - Status and TODO

## Current Sorry Count (as of 2026-02-11)

| File | Sorrys | Key Items |
|------|--------|-----------|
| **StochasticIntegration.lean** | **9** | ito_formula(martingale), quadratic_variation, bdg_inequality, sde_existence, sde_uniqueness_law, stratonovich, semimartingale_integral, girsanov, martingale_representation |
| **BrownianMotion.lean** | **6** | time_inversion, eval_unit_is_brownian, Q-Wiener continuous_paths, Q-Wiener regularity_from_trace, levy_characterization, (t<0 design) |
| **SPDE.lean** | **7** | Generator/semigroup infrastructure |
| **Basic.lean** | **1** | is_martingale_of_bounded (needs uniform integrability) |
| **RegularityStructures.lean** | **1** | Abstract approach (complementary to folder) |
| **Probability/Basic.lean** | **2** | condexp_jensen, doob_maximal_L2 |
| **Probability/IndependenceHelpers.lean** | **0** | Fully proven |
| **Helpers/InnerIntegralIntegrability.lean** | **3** | Tonelli/Fubini infrastructure |
| **Helpers/** (all other) | **0** | 12 files, all fully proven |
| **RegularityStructures/** | **44** | See RegularityStructures/TODO.md |

**Total: 73 sorrys** (29 SPDE core + 44 RegularityStructures)

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

**Statement:**
For C² function f and Itô process dX_t = μ_t dt + σ_t dW_t:
```
f(t, X_t) = f(0, X_0) + ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds + M_t
```
where M_t is a martingale (the stochastic integral ∫₀ᵗ ∂_x f · σ dW).

**Proposed proof strategy (direct partition approach):**

1. **Partition**: Take partitions 0 = t₀ < t₁ < ... < tₙ = t with mesh → 0
2. **Telescope**: f(t, X_t) - f(0, X₀) = Σᵢ [f(tᵢ₊₁, Xᵢ₊₁) - f(tᵢ, Xᵢ)]
3. **Taylor expand each increment** (using `taylor_mean_remainder_bound` from Mathlib):
   - f(tᵢ₊₁, Xᵢ₊₁) - f(tᵢ, Xᵢ) ≈ ∂_t f · Δtᵢ + ∂_x f · ΔXᵢ + ½∂²_x f · (ΔXᵢ)²
4. **Sum the terms**:
   - Σ ∂_t f · Δtᵢ → ∫₀ᵗ ∂_t f ds (Riemann sum convergence)
   - Σ ∂_x f · ΔXᵢ = Σ ∂_x f · (μ Δt + σ ΔW) → drift integral + stochastic integral
   - Σ ½∂²_x f · (ΔXᵢ)² → ½∫₀ᵗ ∂²_x f · σ² ds (key: cross terms vanish, (ΔWᵢ)² → Δtᵢ)
5. **Error control**: Taylor remainder is O(|ΔXᵢ|³) → 0 in L² as mesh → 0

**Key infrastructure needed:**
1. **Riemann sum convergence**: Σᵢ g(tᵢ)·Δtᵢ → ∫₀ᵗ g(s)ds
2. **BM quadratic variation L² convergence**: E[|Σᵢ(ΔWᵢ)² - t|²] → 0
   - Uses: (ΔWᵢ)² - Δtᵢ is mean-zero, Σ → 0 in L²
3. **Cross-term cancellation**: Σᵢ g(tᵢ)·(ΔWᵢ)² → ∫₀ᵗ g(s) ds
4. **Stochastic integral as limit**: Σ ∂_x f(tᵢ, Xᵢ) · σᵢ · ΔWᵢ → stochastic integral

**Existing infrastructure:**
- `ito_integral_martingale_setIntegral` — proves martingale property for L² limits of simple process integrals
- `taylor_mean_remainder_lagrange` — Taylor expansion from Mathlib
- BM increment properties: `increment_variance`, `increment_mean_zero`, `increment_sq_integrable`
- `cross_term_zero` — cross-term vanishing for simple process isometry

**Priority ordering:**
1. Itô formula via direct partition approach
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

### Helpers/ (12 files, 0 sorrys)
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

### Probability/ (1 file 0 sorrys)
- **IndependenceHelpers.lean** — Bridge lemmas for independence

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
- **BM scaling**: c^{-1/2}W_{ct} is BM
- **BM reflection**: -W is BM
- **Reconstruction exists**: explicit construction R(f) = Π_x f(x)

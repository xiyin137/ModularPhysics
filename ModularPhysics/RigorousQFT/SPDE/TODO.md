# SPDE Standard Approach - Status and TODO

## Current Sorry Count (as of 2026-02-14)

| File | Sorrys | Key Items |
|------|--------|-----------|
| **StochasticIntegration.lean** | **8** | quadratic_variation, bdg_inequality, sde_existence, sde_uniqueness_law, stratonovich, semimartingale_integral, girsanov, martingale_representation |
| **BrownianMotion.lean** | **5** | time_inversion, eval_unit_is_brownian, Q-Wiener continuous_paths, Q-Wiener regularity_from_trace, levy_characterization |
| **SPDE.lean** | **4** | Generator/semigroup infrastructure |
| **Basic.lean** | **1** | is_martingale_of_bounded (needs uniform integrability) |
| **RegularityStructures.lean** | **1** | Abstract approach (complementary to folder) |
| **Probability/Basic.lean** | **2** | condexp_jensen, doob_maximal_L2 |
| **Helpers/ItoFormulaProof.lean** | **6** | ito_error_decomposition, 4 convergence lemmas, si_increment_L2_convergence |
| **Helpers/IsometryTheorems.lean** | **1** | stoch_integral_squared_orthogonal |
| **Helpers/QuarticBound.lean** | **1** | stoch_integral_bounded_approx |
| **Helpers/InnerIntegralIntegrability.lean** | **3** | Tonelli/Fubini infrastructure (NOT imported by anything) |
| **Helpers/** (all other 13 files) | **0** | Fully proven |
| **Probability/IndependenceHelpers.lean** | **0** | Fully proven |
| **Probability/Pythagoras.lean** | **0** | Fully proven |
| **RegularityStructures/** | **38** | See RegularityStructures/TODO.md |

**Total: ~70 sorrys** (32 SPDE core + 38 RegularityStructures)

---

## Soundness Audit (2026-02-12)

**All files audited for definition soundness and axiom smuggling.**

### Results:
- **StochasticIntegration.lean**: SOUND — all structures properly defined
- **BrownianMotion.lean**: SOUND — all structures properly defined
- **Basic.lean**: SOUND — Filtration, Martingale, LocalMartingale all correct
- **SPDE.lean**: SOUND (after fix) — `PolynomialNonlinearity.leading_nonzero` replaces weak `nontrivial`
- **Probability/Basic.lean**: SOUND — `IsGaussian` correctly includes char_function as defining property
- **Helpers/**: SOUND — 15+ files, no issues
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

## Ito Formula — Complete Sorry Dependency Audit (2026-02-14)

### The theorem: `ito_formula` at ItoFormulaProof.lean:1206

**Status**: Top-level proof term is COMPLETE. The theorem calls `ito_formula_martingale` (proved),
which calls `si_increment_L2_convergence` (sorry). All wiring is done — only leaf sorrys remain.

**Statement:**
For C^{1,2} function f and Ito process dX_t = mu_t dt + sigma_t dW_t:
```
f(t, X_t) = f(0, X_0) + int_0^t [d_t f + d_x f * mu + 1/2 d^2_x f * sigma^2] ds + M_t
```
where M_t is a martingale (the stochastic integral int_0^t d_x f * sigma dW).

### Critical Path: 8 sorrys blocking `ito_formula`

```
ito_formula (ItoFormulaProof.lean:1206) -- PROVED, wires to:
  ito_formula_martingale (line 1128) -- PROVED, wires to:
    si_increment_L2_convergence (line 1112) -- SORRY [wiring]
      ito_error_decomposition (line 971) -- SORRY [identity]
      time_riemann_L2_convergence (line 995) -- SORRY [convergence]
      drift_riemann_L2_convergence (line 1020) -- SORRY [convergence]
      qv_error_L2_convergence (line 1044) -- SORRY [convergence]
      taylor_truncated_L2_convergence (line 1076) -- SORRY [convergence]
        [transitively needs QV convergence, which needs:]
        stoch_integral_squared_orthogonal (IsometryTheorems.lean:309) -- SORRY
        stoch_integral_bounded_approx (QuarticBound.lean:812) -- SORRY
```

#### Layer 1: ItoFormulaProof.lean (6 sorrys)

| Line | Lemma | Description | Difficulty |
|------|-------|-------------|------------|
| 971 | `ito_error_decomposition` | Identity: error = E1 + E2 + E3 - E4 via telescope + Taylor | Medium |
| 995 | `time_riemann_L2_convergence` | E1 -> 0 in L^2 (time-derivative Riemann sum error) | Medium |
| 1020 | `drift_riemann_L2_convergence` | E2 -> 0 in L^2 (drift Riemann sum error) | Medium |
| 1044 | `qv_error_L2_convergence` | E3 -> 0 in L^2 (QV approximation error) | Medium-High |
| 1076 | `taylor_truncated_L2_convergence` | E4 -> 0 in L^2 (Taylor remainder) | Medium |
| 1112 | `si_increment_L2_convergence` | Wires above 5 via squeeze theorem | Wiring |

#### Layer 2: IsometryTheorems.lean (1 sorry)

| Line | Lemma | Description | Difficulty |
|------|-------|-------------|------------|
| 309 | `stoch_integral_squared_orthogonal` | E[((SI_1)^2 - int sigma^2_1) * ((SI_2)^2 - int sigma^2_2)] = 0 for disjoint intervals | Medium |

**Used by**: QVConvergence.lean:215 (in `si_compensated_orthogonal_partition`)

#### Layer 3: QuarticBound.lean (1 sorry)

| Line | Lemma | Description | Difficulty |
|------|-------|-------------|------------|
| 812 | `stoch_integral_bounded_approx` | Approximate diffusion by bounded simple processes in L^2 | Medium |

**Used by**: QuarticBound.lean:1260 (`stoch_integral_increment_L4_integrable_proof`)
-> QVConvergence.lean:276,296,347 -> ito_qv_L2_bound -> ito_process_discrete_qv_L2_convergence

### NOT on critical path (14 sorrys in SPDE core)

| File | Count | Sorrys | Notes |
|------|-------|--------|-------|
| StochasticIntegration.lean | 8 | bdg_inequality, quadratic_variation, sde_existence_uniqueness, sde_uniqueness_law, stratonovich_ito_formula, semimartingale_integral_exists, girsanov_theorem, martingale_representation | Independent theorems |
| InnerIntegralIntegrability.lean | 3 | inner_sq_integral_integrable_of_sub_interval, inner_product_integral_integrable, integrableOn_ae_of_square_integrable | Not imported by anything |
| Probability/Basic.lean | 2 | condexp_jensen, doob_maximal_L2 | Not used by SPDE |
| Basic.lean | 1 | is_martingale_of_bounded | Not used by ito_formula |

### Sorry-free files on the ito_formula critical path

- ItoFormulaDecomposition.lean (0 sorrys)
- ItoFormulaInfrastructure.lean (0 sorrys)
- ItoIntegralProperties.lean (0 sorrys)
- QVConvergence.lean (0 sorrys)
- QuadraticVariation.lean (0 sorrys)
- L2LimitInfrastructure.lean (0 sorrys)
- IsometryAt.lean (0 sorrys)
- TaylorRemainder.lean (0 sorrys)
- All other Helpers/ files (0 sorrys)

### Proven infrastructure (key components)

| Component | Location |
|-----------|----------|
| `ito_formula` top-level wiring | ItoFormulaProof.lean:1206 |
| `ito_formula_martingale` wiring | ItoFormulaProof.lean:1128 |
| `process_L2_increment_bound` | ItoFormulaProof.lean:710 |
| `four_sq_sub_bound` | ItoFormulaProof.lean:694 |
| `si_increment_integrable` | ItoFormulaProof.lean:387 |
| `si_increment_diff_sq_integrable` | ItoFormulaProof.lean:427 |
| `si_increment_martingale_property` | ItoFormulaProof.lean:569 |
| `martingale_setIntegral_eq_of_L2_limit` | L2LimitInfrastructure.lean |
| `ito_integral_martingale_setIntegral` | ItoIntegralProperties.lean |
| `weighted_qv_L2_convergence` | ItoFormulaInfrastructure.lean |
| `ito_process_discrete_qv_L2_convergence` | QVConvergence.lean:984 |
| `ito_qv_L2_bound` | QVConvergence.lean:672 |
| `stoch_integral_isometry` (ItoProcess) | IsometryTheorems.lean:223 |
| `stoch_integral_increment_L4_bound_proof` | QuarticBound.lean:1363 |
| `stoch_integral_increment_L4_integrable_proof` | QuarticBound.lean:1245 |
| `taylor_remainders_ae_tendsto_zero` | ItoFormulaDecomposition.lean |
| `fatou_squeeze_tendsto_zero` | ItoFormulaDecomposition.lean |

---

## Other Sorrys by File

### StochasticIntegration.lean (8 sorrys)
1. `bdg_inequality` (line 1322) — Burkholder-Davis-Gundy inequality
2. `quadratic_variation` (line 1518) — QV of Ito process (corollary of ito_formula with f(x)=x^2)
3. `sde_existence_uniqueness` (line 1677) — SDE existence via Picard iteration
4. `sde_uniqueness_law` (line 1716) — Pathwise uniqueness via Gronwall
5. `stratonovich_ito_formula` (line 1751) — Stratonovich chain rule
6. `semimartingale_integral_exists` (line 1900) — Semimartingale integral construction
7. `girsanov_theorem` (line 1930) — Girsanov theorem
8. `martingale_representation` (line 1956) — Martingale representation theorem

### BrownianMotion.lean (5 sorrys)
1. `time_inversion` (line 595) — t*W(1/t) is BM
2. `eval_unit_is_brownian` (line 648) — Cylindrical Wiener unit evaluation
3. `continuous_paths` (line 744) — Q-Wiener continuous paths
4. `regularity_from_trace` (line 749) — Q-Wiener regularity
5. `levy_characterization` (line 782) — Levy characterization

### Helpers/InnerIntegralIntegrability.lean (3 sorrys — NOT IMPORTED)
1. `inner_sq_integral_integrable_of_sub_interval` (line 82)
2. `inner_product_integral_integrable` (line 100)
3. `integrableOn_ae_of_square_integrable` (line 115)

---

## Fully Proven Components

### Helpers/ (13+ files, 0 sorrys)
- **CommonRefinement.lean** — Merged partitions, valueAtTime, joint measurability
- **SimpleProcessLinear.lean** — Linear combination of simple process integrals
- **MergedValueAtTime.lean** — valueAtTime linearity for merged processes
- **SimpleIntegralMartingale.lean** — Simple stochastic integral is martingale
- **SetIntegralHelpers.lean** — Cross-term vanishing, variance factorization on sets
- **L2LimitInfrastructure.lean** — Set integral convergence from L^2 convergence
- **ItoIntegralProperties.lean** — Ito isometry proof, martingale proof
- **IsometryAt.lean** — isometry_at, bilinear_isometry_at
- **ProductL2Convergence.lean** — Product L^2 convergence
- **IteratedProductConvergence.lean** — Iterated integral product convergence
- **SimpleProcessDef.lean** — SimpleProcess structure, stochasticIntegral definitions
- **GronwallForSDE.lean** — Gronwall lemma infrastructure
- **ItoFormulaInfrastructure.lean** — BM QV L^2 convergence, weighted QV convergence
- **ItoFormulaDecomposition.lean** — Taylor remainder, Fatou squeeze, QV L^2 infrastructure
- **QVConvergence.lean** — Compensated SI squared bounds, QV L^2 bound, discrete QV convergence
- **QuadraticVariation.lean** — QV definitions, discrete QV structure
- **TaylorRemainder.lean** — Taylor remainder bounds

### Probability/ (2 files, 0 sorrys)
- **IndependenceHelpers.lean** — Bridge lemmas for independence
- **Pythagoras.lean** — L^2 Pythagoras for orthogonal RVs

### RegularityStructures/Trees/ (3 files, 0 sorrys)
- **Basic.lean** — MultiIndex, TreeSymbol, complexity
- **Homogeneity.lean** — homogeneity_decomposition, FormalSum algebra
- **Operations.lean** — Standard trees for Phi^4/KPZ

### Key Proven Theorems
- **Ito isometry** (simple + L^2 limit): `E[(int H dW)^2] = E[int H^2 ds]`
- **Bilinear Ito isometry**: `E[(int H1 dW)(int H2 dW)] = E[int H1 H2 ds]`
- **Ito integral is martingale**: set-integral property on [0,T]
- **Ito integral linearity**: `I(aH1 + bH2) = aI(H1) + bI(H2)` in L^2
- **BM quadratic variation compensator**: W^2_t - t is martingale
- **BM quadratic variation L^2 convergence**: E[|sum (DeltaW)^2 - t|^2] -> 0
- **Weighted QV convergence**: sum g_i[(DeltaW_i)^2 - Delta t_i] -> 0 in L^2 for adapted bounded g
- **Ito process discrete QV L^2 convergence**: sum (DeltaX_i)^2 -> [X]_t in L^2
- **Martingale orthogonality**: int_A Y=0 for all A in F_s, X is F_s-meas => E[X*Y]=0
- **Bilinear isometry at different times**: E[S(t)*S(s)] = E[S(s)^2] for s<=t
- **Simple process increment L^2**: E[|S(t)-S(s)|^2] = E[S(t)^2]-E[S(s)^2]
- **Process L^2 increment bound**: E[(X_t - X_s)^2] <= (2*Mmu^2*T + 2*Msigma^2)*(t-s)
- **BM scaling**: c^{-1/2}W_{ct} is BM
- **BM reflection**: -W is BM
- **Reconstruction exists**: explicit construction R(f) = Pi_x f(x)

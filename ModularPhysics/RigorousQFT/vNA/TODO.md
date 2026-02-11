# vNA Module TODO

## Overview

This module develops von Neumann algebra foundations for rigorous QFT, including:
- Unbounded self-adjoint operators
- Spectral theory via Riesz-Markov-Kakutani (RMK)
- Stone's theorem for one-parameter unitary groups
- Modular theory (Tomita-Takesaki)

## Current Status

### Spectral Theory via RMK (Primary Approach) — Sorry-Free Chain

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/SpectralFunctionalViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralMeasurePolarizedViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralTheoremViaRMK.lean` | Complete | 0 |
| `Spectral/CayleyTransform.lean` | Complete | 0 |
| `Spectral/SpectralViaCayleyRMK.lean` | **Complete** | 0 |
| `Spectral/SigmaAdditivity.lean` | **Complete** | 0 |
| `Spectral/SpectralProjectionLemmas.lean` | Complete | 0 |
| `Spectral/JensenLinearity.lean` | Complete | 0 |

### Unbounded Operators — Fully Proven

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Basic.lean` | Complete | 0 |
| `Unbounded/Graph.lean` | Complete | 0 |

### Measure Theory Infrastructure — Mostly Proven

| File | Status | Sorrys |
|------|--------|--------|
| `MeasureTheory/SpectralIntegral.lean` | Complete | 0 |
| `MeasureTheory/CaratheodoryExtension.lean` | Complete | 0 |
| `MeasureTheory/SpectralStieltjes.lean` | In Progress | ~5 |

### T-P Connection

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/TPConnection.lean` | In Progress | 3 |

### Spectral Theorem & Stone's Theorem

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Spectral.lean` | **In Progress** | 9 (PVM sorry-free; FC connection + step approx sorrys remain) |
| `Unbounded/StoneTheorem.lean` | In Progress | ~9 |

### Legacy CFC Approach (SUPERSEDED — Do Not Pursue)

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/FunctionalCalculusFromCFC.lean` | Superseded | 18+ |
| `Spectral/FunctionalCalculusFromCFC/Basic.lean` | Infrastructure only | 1 |
| `MeasureTheory/SpectralIntegralCauchy.lean` | Superseded | 1 |

## Recent Changes

### SpectralMeasure Definition Fix (CRITICAL)

**Problem**: The `SpectralMeasure` structure had `proj : Set ℝ → (H →L[ℂ] H)` over ALL subsets,
but PVM properties like `inter`, `monotone`, `isIdempotent`, `isSelfAdj` only make sense for
measurable sets. The `spectral_theorem` proof defined `P_raw` via `if MeasurableSet E then ... else 0`,
causing 3 **unprovable** sorrys:
- `inter` for non-measurable E or F (P(E∩F) ≠ 0 possible even when P(F) = 0)
- `monotone` for E measurable, F non-measurable (‖P(E)x‖ ≤ 0 impossible)

**Fix**: Added `MeasurableSet` hypotheses to structure axioms that need them, plus
`proj_nonmeasurable : ∀ E, ¬MeasurableSet E → proj E = 0`. This:
1. Eliminates 3 unprovable sorrys (inter ×2, monotone ×1)
2. Makes the definition mathematically sound
3. All downstream consumers (`complexMeasure`, `functionalCalculus`, `unitaryGroup`, etc.)
   only ever call `proj` on measurable sets, so no downstream breakage

Also removed `MeasurableSet` requirements from `proj_norm_le` and `proj_opNorm_le_one`
(which can handle all sets via case split on measurability).

## Action Plan — Path to Spectral Theorem & Stone's Theorem

### Step 1: ✅ Fix SpectralMeasure definition — DONE
- Added MeasurableSet hypotheses to structure axioms
- Eliminated 3 unprovable sorrys
- All files compile cleanly

### Step 2: ✅ Complete σ-additivity in spectral_theorem — DONE
**File:** `Spectral/SigmaAdditivity.lean` (sorry-free)

Proved `spectralProjection_sigma_additive`: for disjoint measurable Eᵢ,
P(⋃ Eᵢ)x → Σ P(Eᵢ)x in norm.

Strategy used:
- ‖P(⋃ Eᵢ)x - Σⁿ P(Eᵢ)x‖² = ‖P(⋃ Eᵢ)x‖² - Σⁿ ‖P(Eᵢ)x‖² (Pythagorean + orthogonality)
- ‖P(⋃ Eᵢ)x‖² = Σ∞ ‖P(Eᵢ)x‖² (from σ-additivity of spectralMeasureDiagonal)
- Tail of convergent series → 0

### Step 2.5: ✅ Refactor spectral_theorem — DONE
- Created `spectral_theorem_pvm` (sorry-free): PVM construction via RMK chain
- `spectralMeasure` and `spectralCayley` definitions now sorry-free (based on `spectral_theorem_pvm`)
- Added `spectralMeasure_eq_RMK`: sorry-free agreement with RMK construction
- `spectral_theorem` kept as corollary with FC connection sorry
- `spectralMeasure_spec` has explicit sorry for FC connection

### Step 3: Complete TPConnection.lean (3 sorrys)
**File:** `Spectral/TPConnection.lean`

1. `TP_connection` (main): `⟨x, UnboundedCFC T f y⟩ = spectral integral`
   - Use `spectralMeasurePolarized_integral` + dominated convergence
2. `TP_connection_diagonal`: `‖f(T) z‖² = ∫ |f|² dμ_z`
   - Follows from TP_connection by polarization
3. `spectral_theorem_TP_connection`: `⟨x, T y⟩ = μ^ℝ_{x,y}(ℝ)`
   - Requires showing `UnboundedCFC T id = T` on dom(T)

### Step 4: Complete functionalCalculus properties
**File:** `Unbounded/Spectral.lean`

- `stepApproximation_cauchy` (line 578): Riemann sum convergence
- `functionalCalculus` existence (line 753): via sesquilinear form
- `functionalCalculus_mul` (line 770): from P(E∩F)=P(E)P(F)
- `functionalCalculus_star` (line 784): from P(E)*=P(E)
- `functionalCalculus_eq_limit` (line 803): limit uniqueness
- `spectral_theorem` FC connection (line 992)
- `spectralMeasure_spec` (line 1023)

### Step 5: Stone's Theorem — Forward Direction
**File:** `Unbounded/Spectral.lean` (lines 1234-1305) — mostly done!

Once spectral_theorem is complete:
- `U(t) = ∫ exp(itλ) dP(λ)` via `functionalCalculus` — already defined
- Group property: `U(s)U(t) = U(s+t)` — **already proven** (uses `power_add`)
- U(0) = 1 — **already proven** (uses `power_zero`, modulo sorry)
- U(t)* = U(-t) — **already proven** (uses `functionalCalculus_star`)
- Unitarity — **already proven** (uses composition with inverse)
- **Only remaining sorry**: `unitaryGroup_continuous` (line 1305) — dominated convergence

### Step 6: Stone's Theorem — Inverse Direction (HARDEST)
**File:** `Unbounded/StoneTheorem.lean`

1. `generator_densely_defined` (line 339) — needs mollification:
   - Define x_φ = ∫ φ(t) U(t)x dt for test functions φ
   - Show x_φ ∈ dom(A) and Ax_φ = ∫ φ'(t) U(t)x dt
   - Take φ → δ (approximate identity) for density
   - **Infrastructure needed:** Bochner integration of H-valued functions over ℝ

2. `generator_selfadjoint` (line 510) — the hardest sorry:
   - Symmetry (A ⊆ A*) is already proven
   - Need A* ⊆ A: show ∫₀ᵗ U(s)y ds ∈ dom(A) and differentiate
   - **Infrastructure needed:** Resolvent estimates, H-valued integration

### Step 7: Full Stone's theorem + timeEvolution
Once Steps 5-6 are done:
- `Stone.generates`: U(t) = exp(itA) via uniqueness
- `timeEvolution`: Direct construction from spectral integration
- `timeEvolution_generator`: Generator recovery

## Priority/Dependency Order

```
[Step 1]   Fix SpectralMeasure definition            ✅ DONE
    ↓
[Step 2]   Complete sigma_additive                    ✅ DONE
    ↓
[Step 2.5] Refactor spectral_theorem (sorry-free PVM) ✅ DONE
    ↓
[Step 3]   Complete TPConnection.lean (3 sorrys)      ← NEXT
    ↓
[Step 4]   Complete functionalCalculus properties
    ↓
[Step 5]   Stone forward direction                    (mostly proven already)
    ↓
[Step 6]   Stone inverse direction                    ← HARDEST (mollification)
    ↓
[Step 7]   Full Stone's theorem + timeEvolution
```

Steps 1-4 are the critical path for the spectral theorem.
Steps 5-7 complete Stone's theorem.
Step 6 is the hardest and can be worked on independently.

## Sorry Summary by File

| File | Sorrys | Category |
|------|--------|----------|
| `Unbounded/Spectral.lean` | 9 | Step approx (5) + FC connection (2) + power_zero (1) + continuity (1) |
| `Unbounded/StoneTheorem.lean` | ~9 | Stone's theorem (inverse direction hardest) |
| `Spectral/TPConnection.lean` | 3 | T-P connection |
| `MeasureTheory/SpectralStieltjes.lean` | ~5 | Stieltjes measure infrastructure |
| **Total (on critical path)** | **~26** | |

### Sorry-Free Definitions (Key Achievement)
- `spectral_theorem_pvm`: PVM existence (sorry-free)
- `UnboundedOperator.spectralMeasure`: Spectral measure definition (sorry-free)
- `UnboundedOperator.spectralCayley`: Cayley transform definition (sorry-free)
- `UnboundedOperator.spectralMeasure_eq_RMK`: Agreement with RMK (sorry-free)

## What NOT to Pursue

- **CFC approach** (`FunctionalCalculusFromCFC.lean`): 18+ sorrys, superseded by RMK
- **SpectralIntegralCauchy.lean**: Only relevant to CFC Riemann sum approach
- **Non-measurable set handling**: Fixed by definition change

## Key Technical Notes

### Why RMK?

The traditional approach creates circularity:
1. CFC for bounded normal operators → spectral projections
2. Cayley transform to reduce unbounded to bounded
3. But CFC itself uses spectral theory

The RMK approach breaks this by:
1. Defining spectral functional Λ_z(f) = Re⟨z, cfc(f, U) z⟩
2. Using RMK to get a measure μ_z from Λ_z
3. Extending to polarized measure μ_{x,y} via polarization
4. Defining P(E) via sesquilinear form: ⟨x, P(E) y⟩ = μ_{x,y}(E)

### Key Lemmas Available (Sorry-Free)

**From RMK chain:**
- `spectralFunctionalAux_tendsto_of_pointwise_general`: Dominated convergence
- `spectralProjection_polarized_product_closed`: P(E)P(F) product formula
- `spectralProjection_idempotent_closed`: P(F)² = P(F)
- `spectralMeasurePolarized_univ`: μ_{x,y}(Circle) = ⟨x, y⟩
- `spectralMeasurePolarized_integral`: U-P connection for compactly supported
- `one_not_eigenvalue`: U x = x ⟹ x = 0

**From TPConnection.lean:**
- `spectralMeasureDiagonalOnR`: Pullback measure on ℝ
- `TP_connection_indicator`: ⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E)
- `spectralMeasureDiagonal_singleton_one_eq_zero`: μ_z({1}) = 0
- `integral_circle_eq_integral_minus_one`: ∫ g dμ = ∫_{Circle\{1}} g dμ

## References

- Reed-Simon, "Methods of Modern Mathematical Physics I", Ch. VII-VIII
- Rudin, "Functional Analysis", Ch. 13
- Kato, "Perturbation Theory for Linear Operators", Ch. V

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

### Spectral Theorem & Functional Calculus

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Spectral.lean` | **In Progress** | ~7 (PVM + spectral_theorem sorry-free!) |

**Key achievements:**
- `spectral_theorem_pvm`: PVM existence — **sorry-free**
- `spectral_theorem`: `⟨x, f(T)y⟩ = P.spectralIntegral f x y` — **sorry-free**
- `functionalCalculus_star`: `(f(T))* = f̄(T)` — **sorry-free**
- `unitaryGroup_inv`: `U(t)* = U(-t)` — **sorry-free**

**Remaining sorrys in Spectral.lean:**
- `functionalCalculus_mul` — multiplicativity f(T)g(T) = (fg)(T)
- `power` integrability/boundedness (2 sorrys)
- `power_zero`, `power_add` — depend on functionalCalculus_mul
- `unitaryGroup_continuous` — dominated convergence

### Stone's Theorem

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/StoneTheorem.lean` | In Progress | ~9 |

### Deprecated Files (moved to `/backup_deprecated_vNA/`)

The following files used `UnboundedCFC` which is broken for unbounded T
(returns 0 by Mathlib CFC convention). They have been moved out of the
source tree but backed up for reference:
- `TPConnection.lean` — T-P connection via UnboundedCFC
- `FunctionalCalculusFromCFC.lean` — spectral projections via CFC bump operators
- `FunctionalCalculusFromCFC/Basic.lean` — UnboundedCFC definition, proven infrastructure
- `SpectralIntegralCauchy.lean` — Cauchy sequence approach to spectral integrals

## Critical Issue: UnboundedCFC is Broken

**Problem**: `UnboundedCFC T f = cfc (cfcViaInverseCayley f) U` where U is the Cayley
transform. For unbounded T, `1 ∈ σ(U)` and `cfcViaInverseCayley f` is discontinuous
at 1 for most f (since `inverseCayley(w) → ∞` as `w → 1`). By Mathlib's CFC convention,
`cfc g U = 0` when g is not continuous on σ(U). Therefore `UnboundedCFC T f = 0` for most f.

**Fix**: Use `functionalCalculus P f` from `Unbounded/Spectral.lean` which is defined via
the sesquilinear form `Bform P f x y = polarized spectral integral`. This works correctly
for all bounded measurable f and does not depend on the Cayley transform.

**Affected definitions/theorems** (all in `FunctionalCalculusFromCFC/` and `TPConnection.lean`):
- `UnboundedCFC` — returns junk for unbounded T
- `unboundedSpectralFunctional` — uses UnboundedCFC
- `spectralFunctionalCalculus` — uses UnboundedCFC
- `TP_connection` — LHS is UnboundedCFC (= 0 for most f)
- `TP_connection_diagonal` — same issue

## Action Plan

### ✅ Step 1: Fix SpectralMeasure definition — DONE
### ✅ Step 2: Complete σ-additivity — DONE
### ✅ Step 2.5: Refactor spectral_theorem (sorry-free PVM) — DONE
### ✅ Step 3: Prove spectral_theorem — DONE
- Uses `functionalCalculus` (sesquilinear form) instead of `UnboundedCFC`
- Proof: `functionalCalculus_inner` + definitional equality of Bform and spectralIntegral

### Step 4: Complete functionalCalculus properties ← NEXT
**File:** `Unbounded/Spectral.lean`

- `functionalCalculus_mul`: from P(E∩F)=P(E)P(F) via simple function approximation
- `power` integrability/boundedness: need spectral support argument for positive T
- `power_zero`, `power_add`: follow from functionalCalculus_mul
- `unitaryGroup_continuous`: dominated convergence

### Step 5: Stone's Theorem — Forward Direction
**File:** `Unbounded/Spectral.lean`

Once functionalCalculus_mul is complete:
- Group property: `U(s)U(t) = U(s+t)` — uses `power_add`
- U(0) = 1 — uses `power_zero`
- U(t)* = U(-t) — **already proven** (uses `functionalCalculus_star`)
- **Only remaining sorry**: `unitaryGroup_continuous` — dominated convergence

### Step 6: Stone's Theorem — Inverse Direction (HARDEST)
**File:** `Unbounded/StoneTheorem.lean`

1. `generator_densely_defined` — needs mollification
2. `generator_selfadjoint` — the hardest sorry

## Priority/Dependency Order

```
[Steps 1-3]  PVM + spectral_theorem                    ✅ ALL DONE (sorry-free!)
    ↓
[Step 4]     functionalCalculus_mul                     ← NEXT
    ↓
[Step 5]     Stone forward direction                    (mostly proven already)
    ↓
[Step 6]     Stone inverse direction                    ← HARDEST (mollification)
```

## Sorry Summary by File

| File | Sorrys | Category |
|------|--------|----------|
| `Unbounded/Spectral.lean` | 7 | FC mul (1) + power (3) + continuity (1) + FC mul dep (2) |
| `Unbounded/StoneTheorem.lean` | ~9 | Stone's theorem (inverse direction hardest) |
| `MeasureTheory/SpectralStieltjes.lean` | ~5 | Stieltjes measure infrastructure |
| **Total (on critical path)** | **~21** | |

### Sorry-Free Key Results
- `spectral_theorem_pvm`: PVM existence
- `spectral_theorem`: spectral representation ⟨x, f(T)y⟩ = ∫ f d⟨x, P y⟩
- `functionalCalculus_star`: (f(T))* = f̄(T)
- `functionalCalculus_inner`: ⟨x, f(T)y⟩ = Bform P f x y
- `unitaryGroup_inv`: U(t)* = U(-t)
- `UnboundedOperator.spectralMeasure`: spectral measure definition
- `UnboundedOperator.spectralCayley`: Cayley transform definition
- `UnboundedOperator.spectralMeasure_eq_RMK`: agreement with RMK

## What NOT to Pursue

All deprecated files have been moved to `/backup_deprecated_vNA/`:
- **UnboundedCFC**: Broken for unbounded T (returns 0)
- **CFC approach**: Superseded by sesquilinear form
- **TP_connection**: Used broken UnboundedCFC

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

### Why Sesquilinear Form for Functional Calculus?

The `functionalCalculus P f` is defined via:
1. Diagonal measure: `μ_z(E) = ‖P(E)z‖²`
2. Quadratic form: `Q(z) = ∫ f dμ_z`
3. Polarization: `B(x,y) = (1/4)[Q(x+y) - Q(x-y) - iQ(x+iy) + iQ(x-iy)]`
4. Riesz representation: unique T with `⟨x, Ty⟩ = B(x,y)` (sesquilinearToOperator)

This works for ALL bounded measurable f and ANY self-adjoint operator (bounded or unbounded).

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

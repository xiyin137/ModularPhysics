# Nonstandard Analysis Foundation - Status

This document tracks the development of rigorous nonstandard analysis infrastructure for hyperfinite stochastic calculus.

## Current State

**All files build successfully with NO sorries.**

Mathlib provides minimal hyperreal infrastructure:
- `Hyperreal := Germ (hyperfilter ℕ) ℝ` - ultraproduct construction
- `ofSeq`, `IsSt`, `st`, `Infinitesimal`, `Infinite` - basic operations
- `isSt_of_tendsto` - the key bridge theorem

We have built substantial infrastructure on top of this.

## Completed Components

### 1. Foundation Layer (`Foundation/`)

**All files: NO sorries, fully proven**

| File | Key Content |
|------|-------------|
| `Hypernatural.lean` | `Hypernat` type, `omega`, arithmetic, `Infinite` predicate, `timeStepIndex` |
| `HyperfiniteSum.lean` | Sums indexed by hypernaturals, linearity, monotonicity |
| `InternalMembership.lean` | Internal sets, ultrafilter membership, hyperfinite sets |
| `Saturation.lean` | ℵ₁-saturation for countable families of internal sets |

#### Saturation Theory (`Saturation.lean`)

Key definitions and results:
- `CountableInternalFamily` - A countable family of internal sets indexed by ℕ
- `HasFIP` - Internal-level finite intersection property
- `HasStandardFIP` - Standard-level FIP (for each n, n-th level intersection is nonempty)
- `countable_saturation_standard` - Main theorem: HasStandardFIP implies intersection nonempty
- `IsUniform` - Property for families where level sets are constant
- `uniform_hasFIP_implies_hasStandardFIP` - For uniform families, internal FIP ⇒ standard FIP

Note: HasFIP and HasStandardFIP are distinct conditions. The saturation theorem uses
HasStandardFIP directly via a diagonal argument: choosing witnesses xₙ at level n and
forming ofSeq(xₙ) which lies in all internal sets.

### 2. Random Walk (`HyperfiniteRandomWalk.lean`)

**NO sorries, fully proven**

Key theorems:
- `quadratic_variation_eq_time`: For standard k, QV = k·dt exactly
- `st_quadratic_variation_eq_time`: For standard time t, st(QV) = t
- `dt_infinitesimal`: Time step is infinitesimal when N is infinite

Note on finiteness: The theorem `walkAt_stepIndex_finite` was REMOVED because
it's FALSE without probability. Walk values can be infinite for pathological
coin flip sequences. The correct statement requires Loeb measure ("almost surely").

### 3. Stochastic Integration (`HyperfiniteStochasticIntegral.lean`)

**NO sorries, fully proven**

Key theorems:
- `ito_isometry`: Σ(H·ΔW)² = Σ H²·dt exactly
- `integral_infinitesimal_of_standard`: For standard k, the integral is infinitesimal
- `integral_not_infinite_of_standard`: Consequence of above

### 4. Integration (`HyperfiniteIntegration.lean`)

**NO sorries, fully proven**

Key theorem:
- `st_hyperfiniteRiemannSum_eq_integral`: Standard part of hyperfinite Riemann sum equals integral

### 5. Pre-Loeb Measure (`LoebMeasure.lean`)

**NO sorries, well-documented limitations**

What's proven:
- `InternalProbSpace` with probability properties
- `preLoebMeasure` (standard part of internal probability)
- Finite additivity, monotonicity, etc.

What's NOT proven (requires saturation):
- Full Loeb measure construction
- σ-additivity
- Anderson's theorem (pushforward = Wiener)

### 6. White Noise (`HyperfiniteWhiteNoise.lean`)

**NO sorries, fully proven**

Key results:
- White noise as normalized increments
- Covariance structure (ξₖ² = 1/dt)
- Quadratic variation of integrals

## Deleted/Obsolete Files

- `QuadraticVariation.lean`: DELETED - proved wrong theorem (QV ≈ 0 for standard k,
  not QV = t for standard time t). Correct theorem is in `HyperfiniteRandomWalk.lean`.

## What Cannot Be Proven Without Additional Infrastructure

### Now Available: Saturation (ℵ₁-saturation)

The saturation infrastructure is now in `Foundation/Saturation.lean`. This enables:

1. **Loeb measure σ-additivity** - Can now be proven using `countable_saturation_standard`
2. **Almost sure statements** - Require Loeb measure (which requires saturation) ✓
3. **Anderson's theorem** - Now provable in principle with saturation

### Still Requires Transfer Principle

1. More elegant proofs of internal set properties
2. Automatic lifting of standard theorems

### Next Steps

1. Update `LoebMeasure.lean` to use saturation for σ-additivity
2. Prove continuity of Loeb paths almost surely
3. Work toward Anderson's theorem (pushforward = Wiener)

## File Structure

```
Nonstandard/
├── Foundation/
│   ├── Hypernatural.lean        [COMPLETE - no sorries]
│   ├── HyperfiniteSum.lean      [COMPLETE - no sorries]
│   ├── InternalMembership.lean  [COMPLETE - no sorries]
│   └── Saturation.lean          [COMPLETE - no sorries]
├── HyperfiniteRandomWalk.lean   [COMPLETE - no sorries]
├── HyperfiniteWhiteNoise.lean   [COMPLETE - no sorries]
├── HyperfiniteIntegration.lean  [COMPLETE - no sorries]
├── HyperfiniteStochasticIntegral.lean [COMPLETE - no sorries]
├── InternalSets.lean            [older version, may need cleanup]
├── LoebMeasure.lean             [COMPLETE - can now add σ-additivity using saturation]
├── Nonstandard.lean             [module file]
└── TODO.md                      [this file]
```

## Key Design Decisions

1. **No axioms**: Everything built from Mathlib's ultraproduct construction
2. **Hypernat as subtype**: `Hypernat := { x : ℝ* // IsHypernat x }` for type safety
3. **toSeq via Classical.choose**: Extract representative sequences non-constructively
4. **Honest about limitations**: Theorems that require Loeb measure are documented, not sorry'd
5. **Removed false theorems**: `walkAt_stepIndex_finite` was false; removed with explanation

## References

1. Anderson, R. M. "A nonstandard representation for Brownian motion and Itô integration" (1976)
2. Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
3. Lindstrøm, T. "Hyperfinite stochastic integration" (1980s)
4. Albeverio, S. et al. "Nonstandard Methods in Stochastic Analysis and Mathematical Physics"
5. Goldblatt, R. "Lectures on the Hyperreals" - Chapter 11 on internal sets

# Supermanifolds Folder - Issues to Fix

## Summary

The algebraic foundations (Superalgebra.lean, GrassmannAlgebra, Berezinian) are well-developed.
**SuperDomainAlgebra.lean** provides Ring/Algebra instances for SuperDomainFunction.
The main Supermanifold definition now uses proper SuperAlgebra structure.

**Recently Completed:**
- `supercommutative'` theorem - Koszul sign rule for homogeneous elements (PROVEN)
- `mul_assoc'` - Associativity of SuperDomainFunction multiplication (PROVEN)
- `partialEven` smoothness - PROVEN using ContDiff.fderiv_right
- **Supermanifold** now has proper sheaf conditions (locality + gluing)
- **Supermanifold** structure sheaf now returns `SuperAlgebra ℝ` with supercommutativity
- **SuperChart.sheafIso** now properly typed as `RingEquiv` to SuperDomainFunction
- **SuperCoordinates** now has proper parity conditions (evenCoords_even, oddCoords_odd)
- **SuperTransition** removed tautological `overlap_nonempty`, added proper diffeomorphism conditions
- **`partialOdd_odd_derivation'`** - Graded Leibniz rule for odd derivatives (PROVEN)
  - Created `Helpers/PartialOddLeibniz.lean` with sign-related lemmas
  - Created `PartialOddDerivation.lean` with the full proof
  - Key lemma: `leibniz_sign_cancel` for the overlapping case I ∩ J = {a}

---

## Current State of Key Definitions

### Supermanifold (lines ~845-890)
**SIGNIFICANTLY IMPROVED:**
- `structureSheaf : (U : Set body) → IsOpen U → SuperAlgebra ℝ`
- `sections_supercomm : ∀ U hU, SuperCommutative (structureSheaf U hU)`
- Proper sheaf conditions: `sheaf_locality` and `sheaf_gluing`
- `localTriviality` gives RingEquiv to SuperDomainFunction

### SuperChart (lines ~920-942)
**IMPROVED:**
- `bodyCoord_injective`, `bodyCoord_continuous`, `bodyCoord_image_open` (proper conditions)
- `sheafIso : (M.structureSheaf domain domainOpen).carrier ≃+* SuperDomainFunction`

### SuperCoordinates (lines ~948-958)
**IMPROVED:**
- `evenCoords_even : ∀ i, evenCoords i ∈ (...).even`
- `oddCoords_odd : ∀ a, oddCoords a ∈ (...).odd`

### SuperTransition (lines ~980-1000)
**IMPROVED:**
- Removed tautological `overlap_nonempty`
- `bodyTransition_diffeo : ContDiff ℝ ⊤ ...`
- `bodyTransition_inv : ∃ (g : ...), ...`

---

## Remaining Issues

### 1. Sorrys Requiring Proofs

| Location | Declaration | Status | Difficulty |
|----------|-------------|--------|------------|
| Batchelor.lean | `batchelor_theorem` | sorry | HIGH - Deep result |
| Batchelor.lean | `batchelor_splitting` | sorry | HIGH - Deep result |
| ~~PartialOddDerivation.lean~~ | ~~`partialOdd_odd_derivation'`~~ | ~~PROVEN~~ | ~~COMPLETE~~ |

### 2. Remaining Placeholders

#### LocallySuperRingedSpace (~line 224)
- `stalks_local : True` - Needs proper stalk definition as colimits

#### SupermanifoldMorphism (~line 909)
- `pullback_hom : True` - Pullback should be a graded algebra homomorphism

#### SuperAtlas (~line 973)
- `transitions_smooth : True` - Transition functions are smooth

#### SuperVectorBundle (~line 1370-1372)
- `localTriviality : True` - Local trivialization condition
- `transitions : True` - Transition functions in GL(r|s)

#### BerezinianBundle (~line 1435)
- `transitions_berezinian : True` - Transitions are Berezinians

---

## Recommendations for Next Steps

### Immediate
1. ~~**Complete `partialOdd_odd_derivation`**~~ - ✅ DONE (PartialOddDerivation.lean)
2. **Fix BerezinIntegration sorrys** - Integration change of variables
3. **SuperconformalMaps sorrys** - Complete proofs in SuperconformalMaps.lean

### Short-term
4. **Implement LocallySuperRingedSpace.stalks_local** - Define stalks as colimits
5. **SuperVectorBundle local triviality** - Proper formulation

### Long-term
6. **Batchelor theorem** - Deep result requiring global analysis
7. **Full integration theory** - Berezin integral on general supermanifolds

---

## File Status Summary

| File | Status | Key Issues |
|------|--------|------------|
| Superalgebra.lean | Good | Complete algebraic foundations |
| SuperRingCat.lean | Good | Category of supercommutative algebras |
| SuperDomainAlgebra.lean | Good | Ring/Algebra instances proven |
| Supermanifolds.lean | Much Improved | Core definitions now proper |
| PartialOddDerivation.lean | Good | partialOdd_odd_derivation' proven |
| Batchelor.lean | Partial | Batchelor theorem sorrys |
| BerezinIntegration.lean | Partial | Integration sorrys, placeholder conditions |
| SuperconformalMaps.lean | Partial | Some sorrys remain |
| Helpers/SuperMatrix.lean | Good | Berezinian computation rigorous |
| Helpers/PartialOddLeibniz.lean | Good | Sign lemmas for Leibniz rule |

---

## Notes

- **Structure sheaf returns SuperAlgebra ℝ**: This ensures the ℤ/2-grading is part of the definition
- **Local triviality gives Grassmann structure**: The RingEquiv to SuperDomainFunction provides body/soul
- **supercommutative'** proven using reorderSign_comm and ring tactics
- **partialEven** proven using ContDiff.fderiv_right and clm_apply
- **partialOdd_odd_derivation'** proven by case analysis:
  - Case I ∩ J = ∅: Standard Leibniz with sign from commuting derivative past f
  - Case I ∩ J = {a}: Both terms cancel via `(-1)^{|I|-1} + (-1)^|I| = 0`
  - Case |I ∩ J| ≥ 2: Products vanish (overlapping Grassmann indices)

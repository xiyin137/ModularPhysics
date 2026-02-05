/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Group.Nat

/-!
# Extending DVR Valuations to Fraction Fields

For a DVR R with fraction field K = Frac(R), we extend `addVal : R → ℕ∞`
to an integer-valued valuation `extendedVal : K → ℤ` defined by:
- `extendedVal(a/b) = addVal(a) - addVal(b)` for a, b in R, b ≠ 0

## Main Definitions

* `DVRValuation.extendedVal` - The extended valuation K → ℤ

## Main Results

* `extendedVal_zero` - v(0) = 0 by convention
* `extendedVal_mul` - v(fg) = v(f) + v(g)
* `extendedVal_add_min` - v(f+g) ≥ min(v(f), v(g))
* `extendedVal_algebraMap` - v(r) = addVal(r) for r in R

## References

* Mathlib.RingTheory.DiscreteValuationRing.Basic
* Neukirch, "Algebraic Number Theory", Chapter I.3
-/

open scoped Classical

namespace DVRValuation

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-!
## Fraction Field Helpers

Note: Some of these helpers only use IsFractionRing, not IsDomain/IsDiscreteValuationRing.
The linter warnings about unused section variables are expected.
-/

/-- The numerator part of the fraction representation. -/
noncomputable def fracNum (f : K) : R :=
  Classical.choose (IsFractionRing.div_surjective (A := R) f)

/-- The denominator part of the fraction representation. -/
noncomputable def fracDenom (f : K) : R :=
  Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective (A := R) f))

/-- The denominator is a non-zero divisor. -/
theorem fracDenom_mem_nonZeroDivisors (f : K) :
    fracDenom f ∈ nonZeroDivisors R :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective (A := R) f))).1

/-- The denominator is nonzero. -/
theorem fracDenom_ne_zero (f : K) : (fracDenom f : R) ≠ 0 :=
  nonZeroDivisors.ne_zero (fracDenom_mem_nonZeroDivisors f)

/-- The fraction representation is correct. -/
theorem fracData_eq (f : K) :
    algebraMap R K (fracNum f) / algebraMap R K (fracDenom f) = f :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective (A := R) f))).2

/-- If f ≠ 0, then the numerator is nonzero. -/
theorem fracNum_ne_zero_of_ne_zero {f : K} (hf : f ≠ 0) : (fracNum f : R) ≠ 0 := by
  intro h
  have heq : algebraMap R K (fracNum f) / algebraMap R K (fracDenom f) = f := fracData_eq f
  rw [h, map_zero, zero_div] at heq
  exact hf heq.symm

/-!
## DVR Valuation Helpers
-/

/-- For nonzero elements of a DVR, addVal is finite. -/
theorem addVal_ne_top_of_ne_zero {r : R} (hr : r ≠ 0) :
    IsDiscreteValuationRing.addVal R r ≠ ⊤ := by
  simp only [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact hr

/-- Extract natural number value from addVal for nonzero elements. -/
noncomputable def addValNat (r : R) (_ : r ≠ 0) : ℕ :=
  (IsDiscreteValuationRing.addVal R r).toNat

theorem addValNat_eq (r : R) (hr : r ≠ 0) :
    (addValNat r hr : ℕ∞) = IsDiscreteValuationRing.addVal R r := by
  simp only [addValNat]
  rw [ENat.coe_toNat]
  exact addVal_ne_top_of_ne_zero hr

/-!
## Main Definition
-/

/-- Extended valuation from DVR to its fraction field.

    For f = a/b in K, returns v(a) - v(b) where v is the DVR valuation.
    Convention: v(0) = 0 (though mathematically v(0) = +∞). -/
noncomputable def extendedVal : K → ℤ := fun f =>
  if hf : f = 0 then 0
  else
    have hnum : fracNum (R := R) f ≠ 0 := fracNum_ne_zero_of_ne_zero hf
    have hdenom : fracDenom (R := R) f ≠ 0 := fracDenom_ne_zero f
    (addValNat (fracNum f) hnum : ℤ) - (addValNat (fracDenom f) hdenom : ℤ)

/-!
## Basic Properties
-/

/-- v(0) = 0 by our convention. -/
theorem extendedVal_zero : extendedVal (R := R) (0 : K) = 0 := by
  simp [extendedVal]

/-- v(1) = 0. -/
theorem extendedVal_one : extendedVal (R := R) (1 : K) = 0 := by
  simp only [extendedVal]
  split_ifs with h
  · rfl
  · -- 1 = 1/1 in the fraction field
    -- Need to show addValNat(num) = addValNat(denom)
    -- The key is that the valuation doesn't depend on the choice of representation
    sorry

/-- v(fg) = v(f) + v(g) for f, g ≠ 0.

    This extends the multiplicativity of addVal to the fraction field. -/
theorem extendedVal_mul (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    extendedVal (R := R) (f * g) = extendedVal (R := R) f + extendedVal (R := R) g := by
  simp only [extendedVal, dif_neg hf, dif_neg hg]
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  simp only [dif_neg hfg]
  -- For f = a/b and g = c/d, we have fg = (ac)/(bd)
  -- v(fg) = v(ac) - v(bd) = v(a) + v(c) - v(b) - v(d)
  --       = (v(a) - v(b)) + (v(c) - v(d)) = v(f) + v(g)
  -- The key is that the valuation doesn't depend on the choice of representation
  sorry

/-- v(f + g) ≥ min(v(f), v(g)) when f + g ≠ 0 (ultrametric inequality).

    This extends the ultrametric property of addVal. -/
theorem extendedVal_add_min (f g : K) (hfg : f + g ≠ 0) :
    extendedVal (R := R) (f + g) ≥ min (extendedVal (R := R) f) (extendedVal (R := R) g) := by
  -- For f = a/b and g = c/d, we have f + g = (ad + bc)/(bd)
  -- The ultrametric inequality follows from the DVR case
  sorry

/-- v(r) = addValNat(r) for nonzero r in R (embedded into K). -/
theorem extendedVal_algebraMap (r : R) (hr : r ≠ 0) :
    extendedVal (R := R) (algebraMap R K r) = addValNat r hr := by
  simp only [extendedVal]
  have hne : algebraMap R K r ≠ 0 := by
    intro h
    rw [← (algebraMap R K).map_zero] at h
    exact hr (IsFractionRing.injective R K h)
  simp only [dif_neg hne]
  -- algebraMap r has representation r/1, so v(r) = v(r) - v(1) = v(r) - 0 = v(r)
  -- But the actual representation from fracData might differ
  -- Key lemma: the valuation is independent of representation
  sorry

/-- v(f⁻¹) = -v(f) for f ≠ 0. -/
theorem extendedVal_inv (f : K) (hf : f ≠ 0) :
    extendedVal (R := R) f⁻¹ = -extendedVal (R := R) f := by
  simp only [extendedVal, dif_neg hf]
  have hinv : f⁻¹ ≠ 0 := inv_ne_zero hf
  simp only [dif_neg hinv]
  -- For f = a/b, we have f⁻¹ = b/a
  -- v(f⁻¹) = v(b) - v(a) = -(v(a) - v(b)) = -v(f)
  sorry

/-- Units in R have valuation 0 when viewed in K. -/
theorem extendedVal_unit (u : Rˣ) :
    extendedVal (R := R) (algebraMap R K u) = 0 := by
  have hu : (u : R) ≠ 0 := Units.ne_zero u
  rw [extendedVal_algebraMap (u : R) hu]
  -- addVal of a unit is 0
  have hval : IsDiscreteValuationRing.addVal R u = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_of_unit u
  simp only [addValNat]
  rw [hval]
  rfl

end DVRValuation

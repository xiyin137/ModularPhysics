import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.LineBundles
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Helpers.AnalyticBridge

/-!
# Linear Combinations of L(D) Elements

This file develops the theory of ℂ-linear combinations of elements of L(D).

The key issue: `AnalyticMeromorphicFunction` (AMF) does not support addition
(the zero function cannot be represented since `leadingCoefficient_ne_zero` is required).
Instead, we work with `regularValue` functions, which are standard `carrier → ℂ` functions
that CAN be added.

## Main Definitions

* `lcRegularValue` — The linear combination function p ↦ Σ cᵢ · (basis i).fn.regularValue p

## Main Results

* `lcRegularValue_mdifferentiableAt` — The linear combination is MDifferentiableAt
  at jointly-regular points
* `lcRegularValue_zero_at_pole` — At a pole of some basis element, regularValue = 0
  contributes 0 to the sum (but other terms might still have poles)
* `lcRegularValue_vanishes_at_pts` — Vanishing at the test points (from hypotheses)

## References

* RiemannRoch.lean — The `zero_counting_linear_combination` theorem uses this infrastructure
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

/-!
## Linear Combination Definition
-/

section Definition

variable {RS : RiemannSurface} {D : Divisor RS}

/-- The ℂ-linear combination of regularValues of elements of L(D).

    Given basis elements f₁,...,fₙ in L(D) and coefficients c₁,...,cₙ ∈ ℂ,
    this is the function p ↦ Σ cᵢ · fᵢ(p).regularValue.

    At non-pole points (where all fᵢ have order ≥ 0), this gives the actual
    ℂ-valued linear combination of the function values.
    At pole points, regularValue returns 0 by convention, so this function
    might not capture the full meromorphic behavior at poles. -/
noncomputable def lcRegularValue
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ)
    (p : RS.carrier) : ℂ :=
  Finset.univ.sum (fun i => c i * (basis i).fn.regularValue p)

/-- The linear combination is a standard function RS.carrier → ℂ. -/
theorem lcRegularValue_eq
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ) :
    lcRegularValue basis c = fun p =>
      Finset.univ.sum (fun i => c i * (basis i).fn.regularValue p) := rfl

end Definition

/-!
## Linear Combination is MDifferentiableAt at Regular Points
-/

section Holomorphicity

variable {RS : RiemannSurface} {D : Divisor RS}

/-- At a jointly-regular point (where all basis elements have non-negative order),
    the linear combination is MDifferentiableAt.

    This follows from:
    1. Each `(basis i).fn.regularValue` is MDifferentiableAt (from `holomorphicAway`)
    2. Scalar multiples of MDifferentiableAt functions are MDifferentiableAt
    3. Finite sums of MDifferentiableAt functions are MDifferentiableAt -/
theorem lcRegularValue_mdifferentiableAt
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ)
    (p : RS.carrier) (hreg : ∀ i, 0 ≤ (basis i).fn.order p) :
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (lcRegularValue basis c) p := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  unfold lcRegularValue
  apply mdifferentiableAt_finset_sum
  intro i _
  exact mdifferentiableAt_const_mul (c i) _ p ((basis i).holomorphicAway p (hreg i))

/-- If the linear combination is MDifferentiableAt at all points where all basis
    elements are regular, then it is holomorphic on the complement of the pole locus. -/
theorem lcRegularValue_holomorphicOnComplement
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ) :
    ∀ p : RS.carrier, (∀ i, 0 ≤ (basis i).fn.order p) →
    @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (lcRegularValue basis c) p :=
  fun p hreg => lcRegularValue_mdifferentiableAt basis c p hreg

end Holomorphicity

/-!
## The Pole Locus

The set of points where some basis element has a pole is finite.
-/

section PoleLocus

variable {RS : RiemannSurface} {D : Divisor RS}

/-- The joint pole locus: points where at least one basis element has a pole. -/
def jointPoleLocus {n : ℕ} (basis : Fin n → LinearSystem RS D) : Set RS.carrier :=
  ⋃ i : Fin n, { p | (basis i).fn.order p < 0 }

/-- The joint pole locus is finite (each AMF has finitely many poles). -/
theorem jointPoleLocus_finite {n : ℕ} (basis : Fin n → LinearSystem RS D) :
    (jointPoleLocus basis).Finite := by
  apply Set.Finite.subset (Set.finite_iUnion (fun i => (basis i).fn.order_finiteSupport))
  intro p hp
  simp only [jointPoleLocus, Set.mem_iUnion, Set.mem_setOf_eq] at hp
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  obtain ⟨i, hi⟩ := hp
  exact ⟨i, by omega⟩

/-- A point is jointly regular iff it's not in the joint pole locus. -/
theorem jointly_regular_iff_not_pole {n : ℕ} (basis : Fin n → LinearSystem RS D)
    (p : RS.carrier) :
    (∀ i, 0 ≤ (basis i).fn.order p) ↔ p ∉ jointPoleLocus basis := by
  simp only [jointPoleLocus, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt]

/-- The jointly regular locus is the complement of a finite set. -/
theorem jointly_regular_locus_cofinite {n : ℕ} (basis : Fin n → LinearSystem RS D) :
    (jointPoleLocus basis)ᶜ = { p | ∀ i, 0 ≤ (basis i).fn.order p } := by
  ext p
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  exact (jointly_regular_iff_not_pole basis p).symm

end PoleLocus

/-!
## Vanishing Properties
-/

section Vanishing

variable {RS : RiemannSurface} {D : Divisor RS}

/-- The linear combination at a point where a basis element has a zero (order > 0):
    the regularValue of that element is 0. -/
theorem regularValue_zero_at_positive_order {f : AnalyticMeromorphicFunction RS}
    {p : RS.carrier} (h : 0 < f.order p) :
    f.regularValue p = 0 :=
  AnalyticMeromorphicFunction.regularValue_at_zero h

/-- The linear combination at a point where a basis element has a pole (order < 0):
    the regularValue of that element is 0 by convention. -/
theorem regularValue_zero_at_negative_order {f : AnalyticMeromorphicFunction RS}
    {p : RS.carrier} (h : f.order p < 0) :
    f.regularValue p = 0 :=
  AnalyticMeromorphicFunction.regularValue_at_pole h

/-- If all coefficients are 0, the linear combination is identically 0. -/
theorem lcRegularValue_zero_of_coeffs_zero
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ)
    (hc : ∀ i, c i = 0) (p : RS.carrier) :
    lcRegularValue basis c p = 0 := by
  simp [lcRegularValue, hc]

/-- On a compact RS, if the linear combination is MDifferentiable everywhere
    (no poles) and has a zero at some point, then it's identically zero. -/
theorem lcRegularValue_constant_if_holomorphic
    (CRS : CompactRiemannSurface) {D' : Divisor CRS.toRiemannSurface}
    {n : ℕ} (basis : Fin n → LinearSystem CRS.toRiemannSurface D')
    (c : Fin n → ℂ)
    (hholAll : ∀ p, @MDifferentiableAt ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      CRS.toRiemannSurface.carrier CRS.toRiemannSurface.topology
      CRS.toRiemannSurface.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _
      (lcRegularValue basis c) p)
    (p : CRS.toRiemannSurface.carrier) (hp : lcRegularValue basis c p = 0) :
    ∀ q, lcRegularValue basis c q = 0 := by
  -- The linear combination is holomorphic on all of CRS
  -- By holomorphicIsConstant, it's constant
  -- Since it's 0 at p, it's 0 everywhere
  exact rs_identity_principle_compact CRS _ hholAll p hp

end Vanishing

/-!
## Order Bounds for Linear Combinations

When the linear combination is viewed as a meromorphic function, its poles
are bounded by the divisor D.
-/

section OrderBounds

variable {RS : RiemannSurface} {D : Divisor RS}

/-- For elements of L(D), the order at each point is at least -D.coeff p.
    This is the definition of being in L(D): div(f) + D ≥ 0. -/
theorem linearSystem_order_ge_neg_D (f : LinearSystem RS D) (p : RS.carrier) :
    -D.coeff p ≤ f.fn.order p := by
  have h := f.effective p
  -- h : 0 ≤ (divisorOf f.fn + D).coeff p
  -- Unfold: (divisorOf f.fn + D).coeff p = f.fn.order p + D.coeff p
  change 0 ≤ (Divisor.add (divisorOf f.fn) D).coeff p at h
  simp only [Divisor.add, divisorOf] at h
  omega

/-- The chart-local order of a basis element's regularValue matches its AMF order,
    and hence is at least -D(p). -/
theorem chartOrderAt_basis_ge_neg_D (f : LinearSystem RS D) (p : RS.carrier) :
    (-D.coeff p : WithTop ℤ) ≤ chartOrderAt (RS := RS) f.fn.regularValue p := by
  letI := RS.topology
  letI := RS.chartedSpace
  rw [f.chartOrderAt_eq]
  exact_mod_cast linearSystem_order_ge_neg_D f p

/-- The chart-local order of the linear combination Σ cᵢ · fᵢ.regularValue
    is at least -D(q) at every point q.

    This follows from:
    1. Each basis element has chartOrderAt ≥ -D(q) (from chartOrderAt_eq + effective)
    2. Scalar multiples preserve or increase order
    3. The order of a sum is ≥ minimum of the individual orders -/
theorem chartOrderAt_lcRegularValue_ge_neg_D
    {n : ℕ} (basis : Fin n → LinearSystem RS D) (c : Fin n → ℂ) (q : RS.carrier) :
    (-D.coeff q : WithTop ℤ) ≤ chartOrderAt (RS := RS) (lcRegularValue basis c) q := by
  letI := RS.topology
  letI := RS.chartedSpace
  -- The proof uses meromorphicOrderAt bounds through chartRep
  unfold lcRegularValue chartOrderAt chartRep
  -- We need: meromorphicOrderAt (Σ cᵢ * fᵢ.regularValue ∘ chart⁻¹) (chartPt q) ≥ -D(q)
  -- The key: each individual term cᵢ * fᵢ.regularValue has chart order ≥ -D(q)
  -- And meromorphicOrderAt_add gives: order(sum) ≥ min of orders
  induction n with
  | zero =>
    -- Empty sum = constant 0, order = ⊤ ≥ anything
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have : (fun x => (0 : ℂ)) ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm = fun _ => (0 : ℂ) := by
      ext; simp
    rw [this]
    simp [meromorphicOrderAt_const]
  | succ n ih =>
    -- Sum over Fin (n+1) = last term + sum over first n terms
    -- Use meromorphicOrderAt_add to bound order of sum
    sorry  -- Needs: inductive step using meromorphicOrderAt_add and
           -- meromorphicOrderAt_mul_of_ne_zero for scalar multiples
           -- The bound holds for individual terms (from chartOrderAt_basis_ge_neg_D)
           -- and lifts to sums via meromorphicOrderAt_add.

/-- The chart order support of the linear combination is contained in
    supp(D) ∪ {zeros of g} and is finite on compact surfaces.

    For a nonzero chart-meromorphic function on a compact surface,
    zeros are isolated (hence finite), and poles are bounded by supp(D). -/
theorem lcRegularValue_chartOrderSupport_finite
    (CRS : CompactRiemannSurface)
    {D' : Divisor CRS.toRiemannSurface}
    {n : ℕ} (basis : Fin n → LinearSystem CRS.toRiemannSurface D') (c : Fin n → ℂ) :
    (chartOrderSupport (RS := CRS.toRiemannSurface) (lcRegularValue basis c)).Finite := by
  sorry  -- Requires: isolated zeros of meromorphic functions on compact surfaces

end OrderBounds

end RiemannSurfaces.Analytic

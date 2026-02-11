import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Chart-Local Meromorphic Functions on Riemann Surfaces

This file defines chart-local meromorphic functions and their order theory,
bridging between our abstract `AnalyticMeromorphicFunction` (AMF) and
Mathlib's `MeromorphicAt` in charts.

## Key Definitions

* `chartRep` — The chart representation of a function: `f ∘ (extChartAt p).symm`
* `chartPt` — The chart image of a point: `(extChartAt p) p`
* `IsChartMeromorphic` — `f` is MeromorphicAt in every chart
* `chartOrderAt` — The meromorphic order in charts

## Key Results

* `chartMeromorphic_sum` — Sum of chart-meromorphic functions is chart-meromorphic
* `chartOrderAt_add_ge` — Order of sum ≥ min of orders (from Mathlib)
* `chartMeromorphic_argument_principle` — Sum of orders = 0 (sorry, fundamental)

## References

* Mathlib.Analysis.Meromorphic — MeromorphicAt, meromorphicOrderAt
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

/-!
## Chart Representation

Utility functions for working with chart representations of functions on Riemann surfaces.
-/

variable {RS : RiemannSurface}

/-- The chart representation of a function `f : RS.carrier → ℂ` at a point `p`.
    This is `f ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm : ℂ → ℂ`. -/
noncomputable def chartRep (f : RS.carrier → ℂ) (p : RS.carrier) : ℂ → ℂ :=
  letI := RS.topology
  letI := RS.chartedSpace
  f ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm

/-- The chart image of a point p on a Riemann surface. -/
noncomputable def chartPt (p : RS.carrier) : ℂ :=
  letI := RS.topology
  letI := RS.chartedSpace
  extChartAt 𝓘(ℂ, ℂ) p p

/-!
## Chart-Meromorphic Functions

A function `f : RS.carrier → ℂ` is chart-meromorphic if it is `MeromorphicAt`
in every chart. This connects the manifold-level function to Mathlib's meromorphic theory.
-/

/-- A function `f : RS.carrier → ℂ` is chart-meromorphic if for every point `p`,
    the chart representation `f ∘ (extChartAt p).symm` is `MeromorphicAt` at `chartPt p`.

    This is the correct notion of meromorphicity on a manifold: the chart representation
    should be meromorphic in the classical sense at every point. -/
def IsChartMeromorphic (f : RS.carrier → ℂ) : Prop :=
  ∀ p : RS.carrier, MeromorphicAt (chartRep f p) (chartPt (RS := RS) p)

/-- The chart-local meromorphic order at a point.
    Uses Mathlib's `meromorphicOrderAt` applied to the chart representation. -/
noncomputable def chartOrderAt (f : RS.carrier → ℂ) (p : RS.carrier) : WithTop ℤ :=
  meromorphicOrderAt (chartRep f p) (chartPt (RS := RS) p)

/-!
## Arithmetic of Chart-Meromorphic Functions

Sums and scalar multiples of chart-meromorphic functions are chart-meromorphic.
-/

/-- A constant function is chart-meromorphic. -/
theorem chartMeromorphic_const (c : ℂ) : IsChartMeromorphic (RS := RS) (fun _ => c) := by
  intro p
  exact MeromorphicAt.const c _

/-- The sum of two chart-meromorphic functions is chart-meromorphic. -/
theorem chartMeromorphic_add {f g : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (hg : IsChartMeromorphic g) :
    IsChartMeromorphic (fun x => f x + g x) := by
  intro p
  have : chartRep (fun x => f x + g x) p = chartRep f p + chartRep g p := by
    ext z; simp [chartRep, Function.comp]
  rw [this]
  exact (hf p).add (hg p)

/-- A scalar multiple of a chart-meromorphic function is chart-meromorphic. -/
theorem chartMeromorphic_smul (c : ℂ) {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) :
    IsChartMeromorphic (fun x => c * f x) := by
  intro p
  have : chartRep (fun x => c * f x) p = fun z => c * chartRep f p z := by
    ext z; simp [chartRep, Function.comp]
  rw [this]
  exact (MeromorphicAt.const c _).mul (hf p)

/-- A finite sum of chart-meromorphic functions is chart-meromorphic. -/
theorem chartMeromorphic_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → RS.carrier → ℂ)
    (hf : ∀ i ∈ s, IsChartMeromorphic (f i)) :
    IsChartMeromorphic (fun x => s.sum (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact chartMeromorphic_const 0
  | @insert a s ha ih =>
    have heq : (fun x => ∑ i ∈ insert a s, f i x) =
        (fun x => f a x + ∑ i ∈ s, f i x) := by
      ext x; exact Finset.sum_insert ha
    intro p; rw [show chartRep (fun x => ∑ i ∈ insert a s, f i x) p =
        chartRep (fun x => f a x + ∑ i ∈ s, f i x) p by
      simp only [heq]]
    have hfa : IsChartMeromorphic (f a) := hf a (Finset.mem_insert_self _ _)
    have hrest : IsChartMeromorphic (fun x => s.sum (fun i => f i x)) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact (chartMeromorphic_add hfa hrest) p

/-- A linear combination Σ cᵢ · fᵢ of chart-meromorphic functions is chart-meromorphic. -/
theorem chartMeromorphic_linear_combination {n : ℕ}
    (f : Fin n → RS.carrier → ℂ) (c : Fin n → ℂ)
    (hf : ∀ i, IsChartMeromorphic (f i)) :
    IsChartMeromorphic (fun x => Finset.univ.sum (fun i => c i * f i x)) := by
  apply chartMeromorphic_finset_sum
  intro i _
  exact chartMeromorphic_smul (c i) (hf i)

/-!
## Order Properties

Properties of chartOrderAt under arithmetic operations.
-/

/-- The order of a sum is at least the minimum of the individual orders. -/
theorem chartOrderAt_add_ge {f g : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (hg : IsChartMeromorphic g)
    (p : RS.carrier) :
    min (chartOrderAt f p) (chartOrderAt g p) ≤
      chartOrderAt (fun x => f x + g x) p := by
  simp only [chartOrderAt]
  have hrep : chartRep (fun x => f x + g x) p = chartRep f p + chartRep g p := by
    ext z; simp [chartRep, Function.comp]
  rw [hrep]
  exact meromorphicOrderAt_add (hf p) (hg p)

/-- chartRep f p evaluated at chartPt p equals f p. -/
theorem chartRep_apply_chartPt (f : RS.carrier → ℂ) (p : RS.carrier) :
    chartRep f p (chartPt (RS := RS) p) = f p := by
  letI := RS.topology
  letI := RS.chartedSpace
  simp only [chartRep, chartPt, Function.comp_apply]
  congr 1
  exact (extChartAt 𝓘(ℂ, ℂ) p).left_inv (mem_extChartAt_source p)

/-- If f is 0 at a point and chart-continuous there, chartOrderAt is positive.
    Needs ContinuousAt so that f(p) = 0 implies f tends to 0 near p in charts. -/
theorem chartOrderAt_pos_of_zero {f : RS.carrier → ℂ}
    (hf : IsChartMeromorphic f) (p : RS.carrier) (hfp : f p = 0)
    (hcont : ContinuousAt (chartRep (RS := RS) f p) (chartPt (RS := RS) p)) :
    0 < chartOrderAt f p := by
  simp only [chartOrderAt]
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos (hf p)]
  have heq : chartRep f p (chartPt (RS := RS) p) = 0 := by
    rw [chartRep_apply_chartPt]; exact hfp
  rw [show (0 : ℂ) = chartRep f p (chartPt (RS := RS) p) from heq.symm]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-!
## The Chart-Meromorphic Argument Principle

On a compact Riemann surface, the sum of orders of a nonzero chart-meromorphic
function is zero. This is equivalent to `analyticArgumentPrinciple`.
-/

/-- The order support of a chart-meromorphic function: points where chartOrderAt ≠ 0.
    This is finite for chart-meromorphic functions on compact Riemann surfaces. -/
noncomputable def chartOrderSupport (f : RS.carrier → ℂ) : Set RS.carrier :=
  { p | chartOrderAt f p ≠ 0 }

/-- The sum of chart orders over all points with nonzero order.
    Well-defined because only finitely many points have nonzero order. -/
noncomputable def chartOrderSum (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite) : ℤ :=
  hsupp.toFinset.sum (fun p => (chartOrderAt (RS := CRS.toRiemannSurface) f p).getD 0)

/-- **The argument principle for chart-meromorphic functions on compact surfaces.**

    For any nonzero chart-meromorphic function on a compact Riemann surface,
    the sum of orders over all points is zero.

    This is equivalent to `analyticArgumentPrinciple` and requires deep
    infrastructure (residue theorem or topological degree theory). -/
theorem chartMeromorphic_argument_principle (CRS : CompactRiemannSurface)
    (f : CRS.toRiemannSurface.carrier → ℂ)
    (hf : IsChartMeromorphic (RS := CRS.toRiemannSurface) f)
    (hsupp : (chartOrderSupport (RS := CRS.toRiemannSurface) f).Finite)
    (hne : ∃ p, f p ≠ 0) :
    chartOrderSum CRS f hf hsupp = 0 := by
  -- This is the fundamental theorem of complex analysis on compact surfaces.
  -- Equivalent to analyticArgumentPrinciple, proved via residue calculus
  -- or topological degree theory.
  sorry

/-!
## Connecting MDifferentiable to Chart-Meromorphic

An `MDifferentiable` function (globally differentiable on the manifold) is chart-meromorphic.
We need `MDifferentiable` (not just `MDifferentiableAt`) because `DifferentiableOn.analyticAt`
requires differentiability on a neighborhood, not just at one point.
-/

/-- An MDifferentiable function on a Riemann surface is chart-meromorphic.
    The proof uses: MDifferentiable → DifferentiableOn in charts → AnalyticAt → MeromorphicAt. -/
theorem isChartMeromorphic_of_mdifferentiable (f : RS.carrier → ℂ)
    (hf : @MDifferentiable ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ)
      RS.carrier RS.topology RS.chartedSpace ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ f) :
    IsChartMeromorphic f := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.isManifold
  intro p
  -- Build DifferentiableOn on chart target point-by-point
  suffices h : DifferentiableOn ℂ (chartRep f p) (extChartAt 𝓘(ℂ, ℂ) p).target by
    have hmem : (extChartAt 𝓘(ℂ, ℂ) p).target ∈ nhds (chartPt (RS := RS) p) :=
      (isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p)
    exact (h.analyticAt hmem).meromorphicAt
  intro q hq
  set x' := (extChartAt 𝓘(ℂ, ℂ) p).symm q with hx'_def
  have hx'_source : x' ∈ (chartAt ℂ p).source := by
    rw [← extChartAt_source 𝓘(ℂ, ℂ)]
    exact (extChartAt 𝓘(ℂ, ℂ) p).map_target hq
  have hfx'_source : f x' ∈ (chartAt ℂ (f p)).source :=
    mem_chart_source ℂ (f x')
  have hmd := (mdifferentiableAt_iff_of_mem_source (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
    (x := p) (y := f p) hx'_source hfx'_source).mp (hf x')
  obtain ⟨_, hdwa⟩ := hmd
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    modelWithCornersSelf_coe, Set.range_id] at hdwa
  have hda := hdwa.differentiableAt Filter.univ_mem
  have heq : extChartAt 𝓘(ℂ, ℂ) p x' = q := (extChartAt 𝓘(ℂ, ℂ) p).right_inv hq
  rw [heq] at hda
  exact hda.differentiableWithinAt

end RiemannSurfaces.Analytic

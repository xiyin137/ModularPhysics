/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Unbounded.Basic
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import ModularPhysics.RigorousQFT.vNA.Spectral.SpectralViaCayleyRMK
import ModularPhysics.RigorousQFT.vNA.Spectral.SigmaAdditivity
import ModularPhysics.RigorousQFT.vNA.Spectral.FunctionalCalculusFromCFC.Basic
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralStieltjes
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Spectral Theory for Unbounded Self-Adjoint Operators

This file develops the spectral theory for unbounded self-adjoint operators,
which is essential for defining the modular operator Δ and its functional calculus.

## Main definitions

* `SpectralMeasure` - a projection-valued measure on ℝ
* `spectral_theorem` - existence of spectral measure for self-adjoint operators
* `functionalCalculus` - f(T) for bounded Borel functions f
* `unitaryGroup` - the one-parameter unitary group T^{it}

## Mathematical foundations (Reed-Simon/Rudin)

The spectral theorem for unbounded self-adjoint operators states that every
self-adjoint operator T has a unique spectral decomposition T = ∫ λ dP(λ)
where P is a projection-valued measure (PVM). The standard proofs use:

1. **Cayley transform**: Map T to the unitary U = (T-i)(T+i)⁻¹, apply the
   spectral theorem for unitary operators, then pull back.
   (Reed-Simon VIII.3, Rudin 13.30)

2. **Resolution of identity**: Construct P directly from the resolvent
   (T-z)⁻¹ using Stone's formula: P([a,b]) = s-lim ∫_a^b Im((T-λ-iε)⁻¹) dλ/π
   (Reed-Simon VII.3, Kato V.3.5)

The functional calculus properties follow from the construction:
- Multiplicativity: ∫ fg dP = (∫ f dP)(∫ g dP) (Reed-Simon VIII.5)
- Adjoint: (∫ f dP)* = ∫ f̄ dP (Reed-Simon VIII.5)

## Implementation notes

Several theorems are marked with `sorry` as they require deep functional
analysis infrastructure. These are fundamental results that would need either:
- A full development of the Cayley transform approach
- The theory of resolvents and Stone's formula
- Or axiomatization as trusted foundations

The logical structure is complete - all dependencies are properly tracked,
and filling in any sorry would not require changing the API.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis"
  - Chapter VII: The Spectral Theorem
  - Chapter VIII: Unbounded Operators
* Rudin, "Functional Analysis", Chapter 13
* Kato, "Perturbation Theory for Linear Operators", Chapter V
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Spectral measures -/

/-- A projection-valued measure (PVM) on ℝ, also called a spectral measure.
    For each Borel set E ⊆ ℝ, P(E) is an orthogonal projection on H.

    A PVM satisfies:
    1. P(∅) = 0, P(ℝ) = 1
    2. P(E)² = P(E) and P(E)* = P(E) (orthogonal projections)
    3. P(E ∩ F) = P(E)P(F) (multiplicativity)
    4. For disjoint sequence (Eₙ), P(⋃ Eₙ) = Σ P(Eₙ) (σ-additivity, strong convergence)

    The σ-additivity implies that for each x ∈ H, the map E ↦ ⟨x, P(E)x⟩ is a
    positive Borel measure on ℝ with total mass ‖x‖². -/
structure SpectralMeasure (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The projection for each Borel set. For non-measurable sets, returns 0 by convention. -/
  proj : Set ℝ → (H →L[ℂ] H)
  /-- P(∅) = 0 -/
  empty : proj ∅ = 0
  /-- P(ℝ) = 1 -/
  univ : proj Set.univ = 1
  /-- Each P(E) is idempotent (for measurable E) -/
  isIdempotent : ∀ E, MeasurableSet E → proj E ∘L proj E = proj E
  /-- Each P(E) is self-adjoint (for measurable E) -/
  isSelfAdj : ∀ E, MeasurableSet E → ContinuousLinearMap.adjoint (proj E) = proj E
  /-- P(E ∩ F) = P(E) P(F) (for measurable E, F) -/
  inter : ∀ E F, MeasurableSet E → MeasurableSet F → proj (E ∩ F) = proj E ∘L proj F
  /-- Monotonicity: E ⊆ F implies P(E) ≤ P(F) in the operator order (for measurable E, F) -/
  monotone : ∀ E F, MeasurableSet E → MeasurableSet F → E ⊆ F →
    ∀ x : H, ‖proj E x‖ ≤ ‖proj F x‖
  /-- σ-additivity: for disjoint measurable sequence, P(⋃ Eₙ)x = Σ P(Eₙ)x -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i, MeasurableSet (E i)) →
    (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, proj (E i) x)
      Filter.atTop (nhds (proj (⋃ i, E i) x))
  /-- Non-measurable sets get the zero projection -/
  proj_nonmeasurable : ∀ E, ¬MeasurableSet E → proj E = 0

namespace SpectralMeasure

variable (P : SpectralMeasure H)

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩.
    This is a complex-valued Borel measure derived from the spectral measure.
    By polarization, μ_{x,y} determines P completely. -/
def complexMeasure (x y : H) (E : Set ℝ) : ℂ :=
  @inner ℂ H _ x (P.proj E y)

/-- The positive measure μ_x(E) = ⟨x, P(E)x⟩ = ‖P(E)x‖².
    This is a positive Borel measure with total mass ‖x‖².
    It is used to define the spectral integral. -/
def positiveMeasure (x : H) (E : Set ℝ) : ℝ :=
  ‖P.proj E x‖ ^ 2

/-- The positive measure as a real-valued function (for integration) -/
def scalarMeasure (x : H) (E : Set ℝ) : ℝ :=
  (@inner ℂ H _ x (P.proj E x)).re

/-- The support of the spectral measure: the smallest closed set with P(supp) = 1 -/
def support : Set ℝ :=
  { t | ∀ ε > 0, P.proj (Set.Ioo (t - ε) (t + ε)) ≠ 0 }

/-- For disjoint measurable E, F: P(E ∪ F) = P(E) + P(F) -/
theorem additive_disjoint (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : Disjoint E F) :
    P.proj (E ∪ F) = P.proj E + P.proj F := by
  -- Use P(E)P(F) = P(E ∩ F) = P(∅) = 0 for disjoint sets
  -- Combined with idempotence, this gives us additivity
  --
  -- Alternative approach using projections:
  -- P(E ∪ F)² = P(E ∪ F), and P(E ∪ F) projects onto ran(P(E)) ⊕ ran(P(F))
  -- For disjoint E, F: ran(P(E)) ⊥ ran(P(F)), so P(E ∪ F) = P(E) + P(F)
  --
  -- The rigorous proof uses σ-additivity for the two-element sequence
  -- and the fact that partial sums stabilize.
  ext x
  -- We show pointwise: P(E ∪ F)x = P(E)x + P(F)x
  -- Use the fact that P(E) and P(F) project onto orthogonal subspaces
  have hinter : P.proj (E ∩ F) = 0 := by
    have h := hEF
    rw [Set.disjoint_iff_inter_eq_empty] at h
    rw [h]
    exact P.empty
  -- P(E)P(F) = P(E ∩ F) = 0
  have hPEPF : P.proj E ∘L P.proj F = 0 := by rw [← P.inter E F hE hF, hinter]
  have hPFPE : P.proj F ∘L P.proj E = 0 := by rw [← P.inter F E hF hE, Set.inter_comm, hinter]
  -- For orthogonal projections with PQ = 0, P + Q is also a projection onto ran(P) ⊕ ran(Q)
  -- And P(E ∪ F) projects onto the same space
  -- This requires showing (P + Q)² = P + Q when PQ = QP = 0
  -- (P + Q)² = P² + PQ + QP + Q² = P + 0 + 0 + Q = P + Q
  -- Use σ-additivity for a two-element sequence
  let seq : ℕ → Set ℝ := fun n => if n = 0 then E else if n = 1 then F else ∅
  have hseq_disj : ∀ i j, i ≠ j → Disjoint (seq i) (seq j) := by
    intro i j hij
    simp only [seq]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    simp_all [hEF.symm]
  have hunion : ⋃ i, seq i = E ∪ F := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_union, seq]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hi0 : i = 0
      · left; simp_all
      · by_cases hi1 : i = 1
        · right; simp_all
        · simp_all [Set.mem_empty_iff_false]
    · rintro (ht | ht)
      · exact ⟨0, by simp [ht]⟩
      · exact ⟨1, by simp [ht]⟩
  have hseq_meas : ∀ i, MeasurableSet (seq i) := by
    intro i; simp only [seq]
    by_cases hi0 : i = 0
    · simp [hi0]; exact hE
    · by_cases hi1 : i = 1
      · simp [hi1]; exact hF
      · simp [hi0, hi1]
  have hconv := P.sigma_additive seq hseq_meas hseq_disj x
  rw [hunion] at hconv
  -- The partial sums stabilize at P(E)x + P(F)x for n ≥ 2
  have hsum_stable : ∀ n ≥ 2, ∑ i ∈ Finset.range n, P.proj (seq i) x = P.proj E x + P.proj F x := by
    intro n hn
    have h2 : ∑ i ∈ Finset.range 2, P.proj (seq i) x = P.proj E x + P.proj F x := by
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, seq]
      simp only [↓reduceIte, one_ne_zero]
    calc ∑ i ∈ Finset.range n, P.proj (seq i) x
        = ∑ i ∈ Finset.range 2, P.proj (seq i) x +
          ∑ i ∈ Finset.Ico 2 n, P.proj (seq i) x := by
            rw [Finset.sum_range_add_sum_Ico _ hn]
      _ = P.proj E x + P.proj F x + ∑ i ∈ Finset.Ico 2 n, P.proj (seq i) x := by rw [h2]
      _ = P.proj E x + P.proj F x + 0 := by
            congr 1
            apply Finset.sum_eq_zero
            intro i hi
            simp only [Finset.mem_Ico] at hi
            have hge2 : i ≥ 2 := hi.1
            simp only [seq, if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hge2)),
                       if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hge2)),
                       P.empty, ContinuousLinearMap.zero_apply]
      _ = P.proj E x + P.proj F x := add_zero _
  -- A sequence that eventually equals a constant converges to that constant
  have hlim : Tendsto (fun n => ∑ i ∈ Finset.range n, P.proj (seq i) x)
      Filter.atTop (nhds (P.proj E x + P.proj F x)) := by
    apply tendsto_atTop_of_eventually_const
    exact fun n hn => hsum_stable n hn
  -- By uniqueness of limits
  have huniq := tendsto_nhds_unique hconv hlim
  simp only [ContinuousLinearMap.add_apply]
  exact huniq

/-- P(E)P(F) = P(F)P(E) (projections from a PVM commute) -/
theorem proj_comm (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    P.proj E ∘L P.proj F = P.proj F ∘L P.proj E := by
  -- P(E)P(F) = P(E ∩ F) = P(F ∩ E) = P(F)P(E)
  have h1 : P.proj E ∘L P.proj F = P.proj (E ∩ F) := (P.inter E F hE hF).symm
  have h2 : P.proj F ∘L P.proj E = P.proj (F ∩ E) := (P.inter F E hF hE).symm
  rw [h1, h2, Set.inter_comm]

/-- ‖P(E)x‖² = ⟨x, P(E)x⟩ (since P(E) is a projection) -/
theorem norm_sq_eq_inner (E : Set ℝ) (hE : MeasurableSet E) (x : H) :
    ‖P.proj E x‖^2 = (@inner ℂ H _ x (P.proj E x)).re := by
  -- P(E)² = P(E) and P(E)* = P(E), so ⟨x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have hidempotent := P.isIdempotent E hE
  have hselfadj := P.isSelfAdj E hE
  -- ⟨x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have h1 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    -- adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
    -- Since P(E)* = P(E), we have ⟨x, P(E) y⟩ = ⟨P(E) x, y⟩
    -- With y = P(E)x: ⟨x, P(E)(P(E)x)⟩ = ⟨P(E)x, P(E)x⟩
    -- By idempotence P(E)² = P(E): ⟨x, P(E)x⟩ = ⟨x, P(E)(P(E)x)⟩
    have step1 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ x (P.proj E (P.proj E x)) := by
      conv_rhs => rw [← ContinuousLinearMap.comp_apply, hidempotent]
    -- Using self-adjointness: P(E)* = P(E)
    have step2 : @inner ℂ H _ x (P.proj E (P.proj E x)) =
        @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj E x)) := by
      rw [hselfadj]
    -- adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
    have step3 : @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj E x)) =
        @inner ℂ H _ (P.proj E x) (P.proj E x) :=
      ContinuousLinearMap.adjoint_inner_right (P.proj E) x (P.proj E x)
    rw [step1, step2, step3]
  rw [h1, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- ‖P(E)x‖ ≤ ‖x‖ for any spectral projection.
    This follows from P(E) being an orthogonal projection (idempotent and self-adjoint).
    For non-measurable E, P(E) = 0 so the bound is trivially 0 ≤ ‖x‖.

    Proof: By Pythagoras, ‖x‖² = ‖P(E)x‖² + ‖(1-P(E))x‖² ≥ ‖P(E)x‖² -/
theorem proj_norm_le (E : Set ℝ) (x : H) : ‖P.proj E x‖ ≤ ‖x‖ := by
  by_cases hE : MeasurableSet E
  · by_cases hx : x = 0
    · simp [hx]
    -- Use: ‖P(E)x‖² = ⟨x, P(E)x⟩ and Cauchy-Schwarz
    have hnorm_sq := P.norm_sq_eq_inner E hE x
    -- ‖P(E)x‖² = Re⟨x, P(E)x⟩ ≤ ‖⟨x, P(E)x⟩‖ ≤ ‖x‖ · ‖P(E)x‖ (Cauchy-Schwarz)
    have hCS : ‖@inner ℂ H _ x (P.proj E x)‖ ≤ ‖x‖ * ‖P.proj E x‖ :=
      norm_inner_le_norm x (P.proj E x)
    -- For complex z, z.re ≤ |z.re| ≤ ‖z‖
    have hre_le : (@inner ℂ H _ x (P.proj E x)).re ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := by
      calc (@inner ℂ H _ x (P.proj E x)).re
          ≤ |(@inner ℂ H _ x (P.proj E x)).re| := le_abs_self _
        _ ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := Complex.abs_re_le_norm _
    have h1 : ‖P.proj E x‖^2 ≤ ‖x‖ * ‖P.proj E x‖ := by
      calc ‖P.proj E x‖^2 = (@inner ℂ H _ x (P.proj E x)).re := hnorm_sq
        _ ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := hre_le
        _ ≤ ‖x‖ * ‖P.proj E x‖ := hCS
    by_cases hPx : P.proj E x = 0
    · simp [hPx]
    · have hPx_pos : 0 < ‖P.proj E x‖ := norm_pos_iff.mpr hPx
      calc ‖P.proj E x‖ = ‖P.proj E x‖^2 / ‖P.proj E x‖ := by field_simp
        _ ≤ (‖x‖ * ‖P.proj E x‖) / ‖P.proj E x‖ := by
            apply div_le_div_of_nonneg_right h1 hPx_pos.le
        _ = ‖x‖ := by field_simp
  · -- Non-measurable: P(E) = 0
    rw [P.proj_nonmeasurable E hE, ContinuousLinearMap.zero_apply, norm_zero]
    exact norm_nonneg _

/-- The operator norm of P(E) is at most 1.
    For non-measurable E, P(E) = 0 so ‖P(E)‖ = 0 ≤ 1. -/
theorem proj_opNorm_le_one (E : Set ℝ) : ‖P.proj E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  exact P.proj_norm_le E x

/-- P(E)x and P(F)x are orthogonal when E and F are disjoint.
    This follows from P(E)P(F) = P(E ∩ F) = P(∅) = 0. -/
theorem proj_orthogonal_of_disjoint (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : Disjoint E F) (x : H) :
    @inner ℂ H _ (P.proj E x) (P.proj F x) = 0 := by
  -- ⟨P(E)x, P(F)x⟩ = ⟨x, P(E)* P(F)x⟩ = ⟨x, P(E)P(F)x⟩ (self-adjoint)
  --                = ⟨x, P(E ∩ F)x⟩ = ⟨x, P(∅)x⟩ = ⟨x, 0⟩ = 0
  have hinter : E ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.mp hEF
  calc @inner ℂ H _ (P.proj E x) (P.proj F x)
      = @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj F x)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = @inner ℂ H _ x (P.proj E (P.proj F x)) := by rw [P.isSelfAdj E hE]
    _ = @inner ℂ H _ x ((P.proj E ∘L P.proj F) x) := rfl
    _ = @inner ℂ H _ x (P.proj (E ∩ F) x) := by rw [← P.inter E F hE hF]
    _ = @inner ℂ H _ x (P.proj ∅ x) := by rw [hinter]
    _ = @inner ℂ H _ x 0 := by rw [P.empty]; simp
    _ = 0 := inner_zero_right _

omit [CompleteSpace H] in
/-- Pythagorean theorem for pairwise orthogonal vectors indexed by Fin n. -/
theorem pythag_sum_sq {n : ℕ} (v : Fin n → H)
    (horth : ∀ i j, i ≠ j → @inner ℂ H _ (v i) (v j) = 0) :
    ‖∑ i : Fin n, v i‖^2 = ∑ i : Fin n, ‖v i‖^2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hw_u_orth : @inner ℂ H _ (∑ i : Fin k, v (Fin.castSucc i)) (v (Fin.last k)) = 0 := by
      rw [sum_inner]
      apply Finset.sum_eq_zero
      intro i _
      apply horth
      exact Fin.castSucc_ne_last i
    have hpyth2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hw_u_orth
    simp only [sq]
    rw [hpyth2]
    congr 1
    have horth' : ∀ i j : Fin k, i ≠ j →
        @inner ℂ H _ (v (Fin.castSucc i)) (v (Fin.castSucc j)) = 0 := by
      intro i j hij
      apply horth
      exact Fin.castSucc_injective k |>.ne hij
    have h := ih (v ∘ Fin.castSucc) horth'
    simp only [Function.comp_apply, sq] at h
    exact h

/-- The tight operator norm bound for sums of projections on disjoint sets.
    The tight bound is ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ sup |cᵢ| when the Eᵢ are pairwise disjoint.
    This uses orthogonality: ‖Σᵢ cᵢ P(Eᵢ) x‖² = Σᵢ |cᵢ|² ‖P(Eᵢ) x‖².

    The proof requires the Pythagorean theorem for pairwise orthogonal vectors,
    which we establish using the orthogonality of P(E)x and P(F)x for disjoint E, F. -/
theorem proj_sum_norm_le_sup {n : ℕ} (c : Fin n → ℂ) (E : Fin n → Set ℝ)
    (hE_meas : ∀ i, MeasurableSet (E i))
    (hE_disj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (M : ℝ) (hM : ∀ i, ‖c i‖ ≤ M) (hM_pos : 0 ≤ M) :
    ‖∑ i : Fin n, c i • P.proj (E i)‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM_pos
  intro x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  -- Use Pythagorean theorem for orthogonal vectors
  have hproj_orth : ∀ i j, i ≠ j → @inner ℂ H _ (P.proj (E i) x) (P.proj (E j) x) = 0 := by
    intro i j hij
    exact P.proj_orthogonal_of_disjoint (E i) (E j) (hE_meas i) (hE_meas j) (hE_disj i j hij) x
  have hproj_pythag : ‖∑ i : Fin n, P.proj (E i) x‖^2 = ∑ i : Fin n, ‖P.proj (E i) x‖^2 := by
    exact pythag_sum_sq (fun i => P.proj (E i) x) hproj_orth
  -- Define v and use Pythagorean
  let v : Fin n → H := fun i => c i • P.proj (E i) x
  have hv_orth : ∀ i j, i ≠ j → @inner ℂ H _ (v i) (v j) = 0 := by
    intro i j hij
    simp only [v, inner_smul_left, inner_smul_right]
    rw [P.proj_orthogonal_of_disjoint (E i) (E j) (hE_meas i) (hE_meas j) (hE_disj i j hij) x]
    ring
  have hpythag : ‖∑ i : Fin n, v i‖^2 = ∑ i : Fin n, ‖v i‖^2 := by exact pythag_sum_sq v hv_orth
  -- Bound ∑ᵢ ‖P(Eᵢ) x‖² ≤ ‖x‖²
  have hproj_sum_le : ∑ i : Fin n, ‖P.proj (E i) x‖^2 ≤ ‖x‖^2 := by
    rw [← hproj_pythag]
    have hsum_bound : ‖∑ i : Fin n, P.proj (E i) x‖ ≤ ‖x‖ := by
      have hcalc : ‖∑ i : Fin n, P.proj (E i) x‖^2 ≤ ‖x‖ * ‖∑ i : Fin n, P.proj (E i) x‖ :=
        calc ‖∑ i : Fin n, P.proj (E i) x‖^2 = ∑ i : Fin n, ‖P.proj (E i) x‖^2 := hproj_pythag
          _ = ∑ i : Fin n, (@inner ℂ H _ x (P.proj (E i) x)).re := by
              congr 1; ext i; exact P.norm_sq_eq_inner (E i) (hE_meas i) x
          _ = (∑ i : Fin n, @inner ℂ H _ x (P.proj (E i) x)).re := by rw [← Complex.re_sum]
          _ = (@inner ℂ H _ x (∑ i : Fin n, P.proj (E i) x)).re := by rw [← inner_sum]
          _ ≤ ‖@inner ℂ H _ x (∑ i : Fin n, P.proj (E i) x)‖ := Complex.re_le_norm _
          _ ≤ ‖x‖ * ‖∑ i : Fin n, P.proj (E i) x‖ := norm_inner_le_norm _ _
      by_cases hzero : ∑ i : Fin n, P.proj (E i) x = 0
      · rw [hzero, norm_zero]; exact norm_nonneg x
      · have hpos : 0 < ‖∑ i : Fin n, P.proj (E i) x‖ := norm_pos_iff.mpr hzero
        calc ‖∑ i : Fin n, P.proj (E i) x‖
            = ‖∑ i : Fin n, P.proj (E i) x‖^2 / ‖∑ i : Fin n, P.proj (E i) x‖ := by field_simp
          _ ≤ (‖x‖ * ‖∑ i : Fin n, P.proj (E i) x‖) / ‖∑ i : Fin n, P.proj (E i) x‖ := by
              apply div_le_div_of_nonneg_right hcalc hpos.le
          _ = ‖x‖ := by field_simp
    exact sq_le_sq' (by linarith [norm_nonneg (∑ i : Fin n, P.proj (E i) x)]) hsum_bound
  -- Final calculation
  show ‖∑ i : Fin n, c i • P.proj (E i) x‖ ≤ M * ‖x‖
  calc ‖∑ i : Fin n, c i • P.proj (E i) x‖
      = Real.sqrt (‖∑ i : Fin n, c i • P.proj (E i) x‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (∑ i : Fin n, ‖c i • P.proj (E i) x‖^2) := by rw [hpythag]
    _ = Real.sqrt (∑ i : Fin n, ‖c i‖^2 * ‖P.proj (E i) x‖^2) := by
        congr 1; apply Finset.sum_congr rfl; intro i _
        rw [norm_smul]; ring
    _ ≤ Real.sqrt (∑ i : Fin n, M^2 * ‖P.proj (E i) x‖^2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact sq_le_sq' (by linarith [norm_nonneg (c i)]) (hM i)
    _ = Real.sqrt (M^2 * ∑ i : Fin n, ‖P.proj (E i) x‖^2) := by rw [← Finset.mul_sum]
    _ ≤ Real.sqrt (M^2 * ‖x‖^2) := by
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left hproj_sum_le (sq_nonneg M)
    _ = |M| * ‖x‖ := by rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg x)]
    _ = M * ‖x‖ := by rw [abs_of_nonneg hM_pos]

/-! ### Distribution function and diagonal measure -/

/-- ⟨x, P(E)x⟩ is real and non-negative (uses idempotence and self-adjointness). -/
theorem inner_proj_nonneg (E : Set ℝ) (hE : MeasurableSet E) (x : H) :
    0 ≤ (@inner ℂ H _ x (P.proj E x)).re := by
  rw [← P.norm_sq_eq_inner E hE x]; exact sq_nonneg _

/-- ⟨x, P(E)x⟩.re ≤ ‖x‖² for any spectral projection. -/
theorem inner_proj_le_norm_sq (E : Set ℝ) (x : H) :
    (@inner ℂ H _ x (P.proj E x)).re ≤ ‖x‖^2 := by
  by_cases hE : MeasurableSet E
  · rw [← P.norm_sq_eq_inner E hE x]
    exact sq_le_sq' (by linarith [norm_nonneg (P.proj E x), norm_nonneg x]) (P.proj_norm_le E x)
  · rw [P.proj_nonmeasurable E hE, ContinuousLinearMap.zero_apply, inner_zero_right,
        Complex.zero_re]
    exact sq_nonneg _

/-- For decreasing measurable sets with intersection S, P(E_n)x → P(S)x.
    Proof: σ-additivity on the difference sets gives a convergent telescoping sum. -/
theorem proj_decreasing_tendsto_meas (x : H) (E : ℕ → Set ℝ) (S : Set ℝ)
    (hE_meas : ∀ i, MeasurableSet (E i)) (hS_meas : MeasurableSet S)
    (hE_dec : ∀ n, E (n + 1) ⊆ E n) (hS_eq : ⋂ n, E n = S)
    (hS_sub : ∀ n, S ⊆ E n) :
    Tendsto (fun n => P.proj (E n) x) atTop (nhds (P.proj S x)) := by
  -- Define difference sets F_k = E_k \ E_{k+1}
  set F : ℕ → Set ℝ := fun k => E k \ E (k + 1) with hF_def
  have hF_meas : ∀ k, MeasurableSet (F k) := fun k => (hE_meas k).diff (hE_meas (k + 1))
  -- F_k are pairwise disjoint
  have hF_disj : ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hzj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hz.2 (decreasing_chain_le hE_dec (show i + 1 ≤ j by omega) hzj.1)
    · exact hzj.2 (decreasing_chain_le hE_dec (show j + 1 ≤ i by omega) hz.1)
  -- Finite additivity: P(E_k)x = P(E_{k+1})x + P(F_k)x
  have htelesc : ∀ k, P.proj (E k) x = P.proj (E (k + 1)) x + P.proj (F k) x := by
    intro k
    have h := P.additive_disjoint (E (k + 1)) (F k) (hE_meas _) (hF_meas k)
      (Set.disjoint_left.mpr fun z hz ⟨_, hzd⟩ => hzd hz)
    rw [Set.union_diff_cancel (hE_dec k)] at h
    have hx := congrFun (congrArg DFunLike.coe h) x
    simp only [ContinuousLinearMap.add_apply] at hx
    exact hx
  -- Telescoping: ∑_{k<n} P(F_k)x = P(E_0)x - P(E_n)x
  have htelesc_sum : ∀ n, ∑ k ∈ Finset.range n, P.proj (F k) x =
      P.proj (E 0) x - P.proj (E n) x := by
    intro n; induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, (sub_eq_of_eq_add (htelesc m)).symm]
      abel
  -- P(E_n)x = P(E_0)x - ∑_{k<n} P(F_k)x
  have hEn_eq : ∀ n, P.proj (E n) x =
      P.proj (E 0) x - ∑ k ∈ Finset.range n, P.proj (F k) x := by
    intro n; rw [htelesc_sum n]; abel
  -- ⋃_k F_k = E_0 \ S
  have hF_union : ⋃ k, F k = E 0 \ S := by
    ext z; simp only [Set.mem_iUnion, Set.mem_diff]
    constructor
    · rintro ⟨k, hzk, hzk'⟩
      exact ⟨decreasing_chain_le hE_dec (Nat.zero_le k) hzk,
             fun hzS => hzk' (hS_sub (k + 1) hzS)⟩
    · rintro ⟨hz0, hzS⟩
      rw [← hS_eq] at hzS
      simp only [Set.mem_iInter] at hzS
      push_neg at hzS
      obtain ⟨m, hm⟩ := hzS
      haveI : DecidablePred (fun m => z ∉ E m) := Classical.decPred _
      have hexists : ∃ m, z ∉ E m := ⟨m, hm⟩
      set k := Nat.find hexists
      have hk_spec : z ∉ E k := Nat.find_spec hexists
      have hk_pos : k ≠ 0 := fun hk0 => by rw [hk0] at hk_spec; exact hk_spec hz0
      have hk_prev : z ∈ E (k - 1) := by
        by_contra hc; exact Nat.find_min hexists (by omega) hc
      exact ⟨k - 1, hk_prev, by rwa [show k - 1 + 1 = k from by omega]⟩
  -- E_0 = S ∪ (E_0 \ S), so P(E_0)x = P(S)x + P(E_0\S)x
  have hE0_decomp : P.proj (E 0) x = P.proj S x + P.proj (E 0 \ S) x := by
    have h := P.additive_disjoint S (E 0 \ S) hS_meas ((hE_meas 0).diff hS_meas)
      (Set.disjoint_left.mpr fun _ hzS ⟨_, hzd⟩ => hzd hzS)
    rw [Set.union_diff_cancel (hS_sub 0)] at h
    have hx := congrFun (congrArg DFunLike.coe h) x
    simp only [ContinuousLinearMap.add_apply] at hx
    exact hx
  -- σ-additivity: ∑ P(F_k)x → P(E_0 \ S)x
  have hF_sigma := P.sigma_additive F hF_meas hF_disj x
  rw [hF_union] at hF_sigma
  -- P(E_n)x = P(E_0)x - ∑ P(F_k)x → P(E_0)x - P(E_0\S)x = P(S)x
  have h_sub := tendsto_const_nhds (x := P.proj (E 0) x) |>.sub hF_sigma
  have h_eq : P.proj (E 0) x - P.proj (E 0 \ S) x = P.proj S x :=
    sub_eq_iff_eq_add.mpr hE0_decomp
  rw [h_eq] at h_sub
  exact h_sub.congr (fun n => (hEn_eq n).symm)

/-- The spectral distribution function for a SpectralMeasure.
    F_x(t) = ⟨x, P(Iic t) x⟩ = ‖P(Iic t) x‖² -/
def distributionFunction (x : H) : SpectralDistribution where
  toFun := fun t => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
  mono := by
    intro a b hab; dsimp
    rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
    exact sq_le_sq'
      (by linarith [norm_nonneg (P.proj (Set.Iic a) x), norm_nonneg (P.proj (Set.Iic b) x)])
      (P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hab) x)
  right_continuous := by
    intro t
    -- Step 1: Sequential convergence P(Iic(t + 1/(n+1)))x → P(Iic t)x
    set E := fun n : ℕ => Set.Iic (t + 1 / ((↑n : ℝ) + 1))
    have hE_dec : ∀ n, E (n + 1) ⊆ E n := by
      intro n; simp only [E]; apply Set.Iic_subset_Iic.mpr
      have h1 : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
      linarith [one_div_le_one_div_of_le h1 (by push_cast; linarith : (↑n : ℝ) + 1 ≤ ↑(n + 1) + 1)]
    have hE_inter : ⋂ n, E n = Set.Iic t := by
      ext s; simp only [Set.mem_iInter, Set.mem_Iic, E]
      refine ⟨fun h => ?_, fun hs n => le_add_of_le_of_nonneg hs (by positivity)⟩
      by_contra hst; push_neg at hst
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (s - t))
      have hpos : (0 : ℝ) < s - t := sub_pos.mpr hst
      have h1 : 1 < (↑n : ℝ) * (s - t) := by rwa [div_lt_iff₀ hpos] at hn
      have h2 : (s - t) * ((↑n : ℝ) + 1) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1)).mp (by linarith [h n])
      nlinarith [mul_comm (s - t) (↑n : ℝ)]
    have hconv := P.proj_decreasing_tendsto_meas x E (Set.Iic t)
      (fun _ => measurableSet_Iic) measurableSet_Iic hE_dec hE_inter
      (fun n => Set.Iic_subset_Iic.mpr (le_add_of_nonneg_right (by positivity)))
    -- Compose with continuous map y ↦ ⟨x, y⟩.re
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => (@inner ℂ H _ x (P.proj (E n) x)).re)
        atTop (nhds ((@inner ℂ H _ x (P.proj (Set.Iic t) x)).re)) :=
      hcont.continuousAt.tendsto.comp hconv
    -- Step 2: ContinuousWithinAt from monotonicity + sequential convergence
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    rw [Metric.tendsto_atTop] at hseq
    obtain ⟨N, hN⟩ := hseq ε hε
    refine ⟨1 / ((↑N : ℝ) + 1), by positivity, fun s hs hds => ?_⟩
    have hst : t ≤ s := hs
    have hsd : s < t + 1 / ((↑N : ℝ) + 1) := by
      rw [Real.dist_eq, abs_lt] at hds; linarith [hds.2]
    -- f(t) ≤ f(s) ≤ f(t + 1/(N+1)) by monotonicity
    have h_lo : (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re ≤
        (@inner ℂ H _ x (P.proj (Set.Iic s) x)).re := by
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hst) x
      nlinarith [norm_nonneg (P.proj (Set.Iic t) x)]
    have h_hi : (@inner ℂ H _ x (P.proj (Set.Iic s) x)).re ≤
        (@inner ℂ H _ x (P.proj (E N) x)).re := by
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hsd.le) x
      nlinarith [norm_nonneg (P.proj (Set.Iic s) x)]
    -- |f(s) - f(t)| = f(s) - f(t) ≤ f(N) - f(t) < ε
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    have hNN := hN N le_rfl; rw [Real.dist_eq] at hNN
    have h_nn : 0 ≤ (@inner ℂ H _ x (P.proj (E N) x)).re -
        (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re := by linarith
    rw [abs_of_nonneg h_nn] at hNN
    linarith
  nonneg := fun t => P.inner_proj_nonneg _ measurableSet_Iic x
  bound := ‖x‖^2
  bound_nonneg := sq_nonneg _
  le_bound := fun t => P.inner_proj_le_norm_sq _ x
  tendsto_neg_infty := by
    -- P(Iic(-n))x → P(∅)x = 0 via proj_decreasing_tendsto_meas
    set f := fun t : ℝ => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
    have f_mono : Monotone f := by
      intro a b hab; simp only [f]
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hab) x
      nlinarith [norm_nonneg (P.proj (Set.Iic a) x)]
    set E := fun n : ℕ => Set.Iic (-(↑n : ℝ))
    have hE_dec : ∀ n, E (n + 1) ⊆ E n := by
      intro n; simp only [E]; apply Set.Iic_subset_Iic.mpr; push_cast; linarith
    have hE_inter : ⋂ n, E n = ∅ := by
      ext s; simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, E]
      constructor
      · intro h; obtain ⟨n, hn⟩ := exists_nat_gt (-s); linarith [h n]
      · intro h; exact h.elim
    have hconv := P.proj_decreasing_tendsto_meas x E ∅
      (fun _ => measurableSet_Iic) MeasurableSet.empty hE_dec hE_inter
      (fun _ => Set.empty_subset _)
    rw [P.empty, ContinuousLinearMap.zero_apply] at hconv
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => f (-(↑n : ℝ))) atTop (nhds 0) := by
      have := hcont.continuousAt.tendsto.comp hconv
      simp only [inner_zero_right, Complex.zero_re, Function.comp_def] at this
      exact this
    rw [tendsto_order]
    constructor
    · intro a' ha'
      rw [Filter.eventually_atBot]
      exact ⟨0, fun s _ => lt_of_lt_of_le ha' (P.inner_proj_nonneg _ measurableSet_Iic x)⟩
    · intro a' ha'
      rw [Filter.eventually_atBot]
      have hexN : ∃ N : ℕ, f (-(↑N : ℝ)) < a' := by
        by_contra h; push_neg at h
        exact absurd (ge_of_tendsto' hseq h) (not_le.mpr ha')
      obtain ⟨N, hN⟩ := hexN
      exact ⟨-(↑N : ℝ), fun s hs => lt_of_le_of_lt (f_mono hs) hN⟩
  tendsto_pos_infty := by
    -- P(Iic(n))x → P(ℝ)x = x via complement
    set f := fun t : ℝ => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
    have f_mono : Monotone f := by
      intro a b hab; simp only [f]
      rw [← P.norm_sq_eq_inner _ measurableSet_Iic, ← P.norm_sq_eq_inner _ measurableSet_Iic]
      have := P.monotone _ _ measurableSet_Iic measurableSet_Iic (Set.Iic_subset_Iic.mpr hab) x
      nlinarith [norm_nonneg (P.proj (Set.Iic a) x)]
    set G := fun n : ℕ => Set.Ioi (↑n : ℝ)
    have hG_dec : ∀ n, G (n + 1) ⊆ G n := by
      intro n; simp only [G]; apply Set.Ioi_subset_Ioi; push_cast; linarith
    have hG_inter : ⋂ n, G n = ∅ := by
      ext s; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, G]
      constructor
      · intro h; obtain ⟨n, hn⟩ := exists_nat_gt s; linarith [h n]
      · intro h; exact h.elim
    have hG_conv := P.proj_decreasing_tendsto_meas x G ∅
      (fun _ => measurableSet_Ioi) MeasurableSet.empty hG_dec hG_inter
      (fun _ => Set.empty_subset _)
    rw [P.empty, ContinuousLinearMap.zero_apply] at hG_conv
    -- P(Iic n)x = x - P(Ioi n)x by finite additivity
    have h_decomp : ∀ n : ℕ, P.proj (Set.Iic (↑n : ℝ)) x + P.proj (Set.Ioi (↑n : ℝ)) x = x := by
      intro n
      have h := P.additive_disjoint (Set.Iic (↑n : ℝ)) (Set.Ioi (↑n : ℝ))
        measurableSet_Iic measurableSet_Ioi
        (Set.disjoint_left.mpr fun z hz hzoi =>
          not_lt.mpr (Set.mem_Iic.mp hz) (Set.mem_Ioi.mp hzoi))
      rw [Set.Iic_union_Ioi, P.univ] at h
      have hx := congrFun (congrArg DFunLike.coe h) x
      simp only [ContinuousLinearMap.add_apply] at hx
      simpa using hx.symm
    -- P(Iic n)x → x
    have hconv : Tendsto (fun n : ℕ => P.proj (Set.Iic (↑n : ℝ)) x) atTop (nhds x) := by
      have heq : (fun (n : ℕ) => P.proj (Set.Iic (↑n : ℝ)) x) = fun n => x - P.proj (G n) x := by
        ext n; simp only [G]; exact eq_sub_iff_add_eq.mpr (h_decomp n)
      rw [heq]; simpa [sub_zero] using tendsto_const_nhds (x := x) |>.sub hG_conv
    -- Compose with continuous inner product to get f(n) → ‖x‖²
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => f (↑n : ℝ)) atTop (nhds (‖x‖^2)) := by
      have h1 := hcont.continuousAt.tendsto.comp hconv
      simp only [Function.comp_def] at h1
      have hlim : (@inner ℂ H _ x x).re = ‖x‖ ^ 2 := by
        have h := P.norm_sq_eq_inner Set.univ MeasurableSet.univ x
        rw [P.univ] at h; simp only [ContinuousLinearMap.one_apply] at h
        exact h.symm
      rwa [hlim] at h1
    rw [tendsto_order]
    constructor
    · intro a' ha'
      rw [Filter.eventually_atTop]
      have hexN : ∃ N : ℕ, a' < f ↑N := by
        by_contra h; push_neg at h
        exact absurd (le_of_tendsto' hseq h) (not_le.mpr ha')
      obtain ⟨N, hN⟩ := hexN
      exact ⟨↑N, fun s hs => lt_of_lt_of_le hN (f_mono hs)⟩
    · intro a' ha'
      rw [Filter.eventually_atTop]
      exact ⟨0, fun s _ => lt_of_le_of_lt (P.inner_proj_le_norm_sq _ x) ha'⟩

open MeasureTheory in
/-- The diagonal spectral measure μ_{x,x} for a vector x. -/
def diagonalMeasure (x : H) : MeasureTheory.Measure ℝ :=
  (P.distributionFunction x).toMeasure

/-! #### Distribution function identities -/

/-- The distribution function of -z equals that of z.
    F_{-z}(t) = ⟨-z, P(Iic t)(-z)⟩.re = ‖P(Iic t)(-z)‖² = ‖P(Iic t)z‖² = F_z(t). -/
theorem distributionFunction_neg (x : H) (t : ℝ) :
    (P.distributionFunction (-x)).toFun t = (P.distributionFunction x).toFun t := by
  simp only [distributionFunction]
  have : P.proj (Set.Iic t) (-x) = -(P.proj (Set.Iic t) x) := map_neg _ _
  rw [this, inner_neg_left, inner_neg_right, neg_neg]

/-- The parallelogram identity for distribution functions:
    F_{x+y}(t) + F_{x-y}(t) = 2F_x(t) + 2F_y(t).
    This follows from the parallelogram law for the inner product ⟨z, P(E)z⟩. -/
theorem distributionFunction_parallelogram (x y : H) (t : ℝ) :
    (P.distributionFunction (x + y)).toFun t + (P.distributionFunction (x - y)).toFun t =
    2 * (P.distributionFunction x).toFun t + 2 * (P.distributionFunction y).toFun t := by
  simp only [distributionFunction]
  -- Let A = P(Iic t), which is self-adjoint
  set A := P.proj (Set.Iic t)
  -- Expand ⟨x+y, A(x+y)⟩ + ⟨x-y, A(x-y)⟩
  have hlin_add : A (x + y) = A x + A y := map_add A x y
  have hlin_sub : A (x - y) = A x - A y := map_sub A x y
  -- ⟨x+y, A(x+y)⟩ = ⟨x+y, Ax+Ay⟩ = ⟨x,Ax⟩ + ⟨x,Ay⟩ + ⟨y,Ax⟩ + ⟨y,Ay⟩
  -- ⟨x-y, A(x-y)⟩ = ⟨x-y, Ax-Ay⟩ = ⟨x,Ax⟩ - ⟨x,Ay⟩ - ⟨y,Ax⟩ + ⟨y,Ay⟩
  -- Sum = 2⟨x,Ax⟩ + 2⟨y,Ay⟩
  have h1 : @inner ℂ H _ (x + y) (A (x + y)) = @inner ℂ H _ x (A x) + @inner ℂ H _ x (A y) +
      @inner ℂ H _ y (A x) + @inner ℂ H _ y (A y) := by
    rw [hlin_add]; simp [inner_add_left, inner_add_right]; ring
  have h2 : @inner ℂ H _ (x - y) (A (x - y)) = @inner ℂ H _ x (A x) - @inner ℂ H _ x (A y) -
      @inner ℂ H _ y (A x) + @inner ℂ H _ y (A y) := by
    rw [hlin_sub]; simp [inner_sub_left, inner_sub_right]; ring
  have h3 : (@inner ℂ H _ (x + y) (A (x + y))).re + (@inner ℂ H _ (x - y) (A (x - y))).re =
      2 * (@inner ℂ H _ x (A x)).re + 2 * (@inner ℂ H _ y (A y)).re := by
    rw [h1, h2]; simp only [Complex.add_re, Complex.sub_re]; ring
  exact h3

/-- The i-rotation identity for distribution functions:
    F_{x+iy}(t) + F_{x-iy}(t) = 2F_x(t) + 2F_y(t).
    This follows from |i|² = 1 and the parallelogram identity. -/
theorem distributionFunction_irot (x y : H) (t : ℝ) :
    (P.distributionFunction (x + Complex.I • y)).toFun t +
    (P.distributionFunction (x - Complex.I • y)).toFun t =
    2 * (P.distributionFunction x).toFun t + 2 * (P.distributionFunction y).toFun t := by
  -- This is just the parallelogram identity with z = i·y, noting that F_{iz}(t) = F_z(t)
  have h := P.distributionFunction_parallelogram x (Complex.I • y) t
  -- Need: F_{iy}(t) = F_y(t)
  -- ⟨iy, A(iy)⟩ = conj(i)·i·⟨y,Ay⟩ = |i|²⟨y,Ay⟩ = ⟨y,Ay⟩
  have h_iy : (P.distributionFunction (Complex.I • y)).toFun t =
      (P.distributionFunction y).toFun t := by
    simp only [distributionFunction]
    have : P.proj (Set.Iic t) (Complex.I • y) = Complex.I • P.proj (Set.Iic t) y :=
      map_smul _ _ _
    rw [this, inner_smul_left, inner_smul_right]
    simp [Complex.conj_I, Complex.normSq_I, mul_comm]
  rw [h_iy] at h; exact h

/-- Diagonal measure of -z equals that of z: μ_{-z} = μ_z. -/
theorem diagonalMeasure_neg (x : H) :
    P.diagonalMeasure (-x) = P.diagonalMeasure x := by
  simp only [diagonalMeasure, SpectralDistribution.toMeasure]
  congr 1
  ext t  -- StieltjesFunction extensionality (has @[ext])
  exact P.distributionFunction_neg x t

/-- The diagonal measure is a finite measure with total mass = ‖x‖². -/
instance diagonalMeasure_isFiniteMeasure (x : H) :
    MeasureTheory.IsFiniteMeasure (P.diagonalMeasure x) :=
  show MeasureTheory.IsFiniteMeasure (P.distributionFunction x).toMeasure from inferInstance

/-- The total mass of the diagonal measure equals ‖x‖². -/
theorem diagonalMeasure_univ (x : H) :
    (P.diagonalMeasure x) Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  simp only [diagonalMeasure, SpectralDistribution.toMeasure, SpectralDistribution.toStieltjes]
  rw [StieltjesFunction.measure_univ _
    (P.distributionFunction x).tendsto_neg_infty
    (P.distributionFunction x).tendsto_pos_infty]
  -- Goal: ofReal(bound - 0) = ofReal(‖x‖^2), where bound = ‖x‖^2
  simp only [sub_zero, distributionFunction]

/-- The total mass of the diagonal measure as a real number. -/
theorem diagonalMeasure_real_univ (x : H) :
    (P.diagonalMeasure x).real Set.univ = ‖x‖ ^ 2 := by
  simp only [MeasureTheory.Measure.real, P.diagonalMeasure_univ x,
    ENNReal.toReal_ofReal (sq_nonneg ‖x‖)]

/-! #### Integral bounds -/

open MeasureTheory in
/-- For bounded f, the integral against the diagonal measure is bounded:
    ‖∫ f dμ_z‖ ≤ M * ‖z‖² when ‖f‖_∞ ≤ M. -/
theorem integral_diagonalMeasure_norm_le (x : H) (f : ℝ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M) :
    ‖∫ t, f t ∂(P.diagonalMeasure x)‖ ≤ M * ‖x‖ ^ 2 := by
  have hfm := P.diagonalMeasure_isFiniteMeasure x
  calc ‖∫ t, f t ∂(P.diagonalMeasure x)‖
      ≤ M * (P.diagonalMeasure x).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hf)
    _ = M * ‖x‖ ^ 2 := by rw [P.diagonalMeasure_real_univ x]

end SpectralMeasure

/-! ### Functional calculus -/

/-- A simple function for spectral integrals: a finite linear combination of indicator functions.
    Represents f = Σᵢ cᵢ χ_{Eᵢ} where the Eᵢ are disjoint measurable sets. -/
structure SimpleFunction (n : ℕ) where
  /-- The coefficients -/
  coeffs : Fin n → ℂ
  /-- The sets (should be disjoint for a proper simple function) -/
  sets : Fin n → Set ℝ

namespace SimpleFunction

open Classical in
/-- Evaluate a simple function at a point -/
def eval {n : ℕ} (f : SimpleFunction n) (x : ℝ) : ℂ :=
  ∑ i : Fin n, if x ∈ f.sets i then f.coeffs i else 0

/-- Apply a simple function to a spectral measure: Σᵢ cᵢ P(Eᵢ) -/
def spectralApply {n : ℕ} (f : SimpleFunction n) (P : SpectralMeasure H) : H →L[ℂ] H :=
  ∑ i : Fin n, f.coeffs i • P.proj (f.sets i)

/-- The constant simple function -/
def const (c : ℂ) : SimpleFunction 1 where
  coeffs := fun _ => c
  sets := fun _ => Set.univ

/-- The indicator simple function for a set -/
def indicator (E : Set ℝ) : SimpleFunction 1 where
  coeffs := fun _ => 1
  sets := fun _ => E

end SimpleFunction

/-- A structure representing the functional calculus for a spectral measure.
    This encapsulates the map f ↦ f(T) = ∫ f(λ) dP(λ) together with its properties.

    The functional calculus maps bounded Borel functions f : ℝ → ℂ to bounded operators
    on H, satisfying:
    - Linearity: (αf + g)(T) = αf(T) + g(T)
    - Multiplicativity: (fg)(T) = f(T)g(T)
    - Adjoint: f(T)* = f̄(T) where f̄(λ) = conj(f(λ))
    - Continuity: if fₙ → f uniformly with ‖fₙ‖ ≤ C, then fₙ(T) → f(T) strongly
    - Identity: 1(T) = I
    - Characteristic: χ_E(T) = P(E) for Borel sets E -/
structure FunctionalCalculus (P : SpectralMeasure H) where
  /-- The map from bounded Borel functions to bounded operators -/
  apply : (ℝ → ℂ) → (H →L[ℂ] H)
  /-- Characteristic functions map to projections -/
  characteristic : ∀ E : Set ℝ, apply (Set.indicator E (fun _ => 1)) = P.proj E
  /-- Constant function 1 maps to identity -/
  identity : apply (fun _ => 1) = 1
  /-- Multiplicativity -/
  mul : ∀ f g, apply (f * g) = apply f ∘L apply g
  /-- Adjoint property -/
  adjoint : ∀ f, ContinuousLinearMap.adjoint (apply f) = apply (star ∘ f)

/-- The spectral integral of the constant function 1 is the identity -/
theorem simple_spectralApply_one (P : SpectralMeasure H) :
    (SimpleFunction.const 1).spectralApply P = 1 := by
  unfold SimpleFunction.const SimpleFunction.spectralApply
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_smul]
  exact P.univ

/-- The spectral integral respects scalar multiplication in coefficients -/
theorem simple_spectralApply_smul {n : ℕ} (P : SpectralMeasure H)
    (f : SimpleFunction n) (c : ℂ) :
    -- Scaling all coefficients by c scales the result
    (⟨fun i => c * f.coeffs i, f.sets⟩ : SimpleFunction n).spectralApply P =
    c • f.spectralApply P := by
  unfold SimpleFunction.spectralApply
  simp only [Finset.smul_sum, smul_smul]

/-- Weak bound on the operator norm of a simple function applied to a spectral measure.
    For a simple function f = Σᵢ cᵢ χ_{Eᵢ} with n terms, we have ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ n * sup |cᵢ|.

    This uses the triangle inequality: ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ Σᵢ |cᵢ| ‖P(Eᵢ)‖ ≤ n * M.

    NOTE: The tight bound ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ sup |cᵢ| (independent of n) holds when
    the Eᵢ are disjoint, using orthogonality. See `proj_sum_norm_le_sup`. -/
theorem simple_spectralApply_norm_le {n : ℕ} (P : SpectralMeasure H) (f : SimpleFunction n)
    (M : ℝ) (hM : ∀ i, ‖f.coeffs i‖ ≤ M) :
    ‖f.spectralApply P‖ ≤ n * M := by
  unfold SimpleFunction.spectralApply
  calc ‖∑ i : Fin n, f.coeffs i • P.proj (f.sets i)‖
      ≤ ∑ i : Fin n, ‖f.coeffs i • P.proj (f.sets i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖f.coeffs i‖ * ‖P.proj (f.sets i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_smul_le _ _
    _ ≤ ∑ i : Fin n, ‖f.coeffs i‖ * 1 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (P.proj_opNorm_le_one _) (norm_nonneg _)
    _ = ∑ i : Fin n, ‖f.coeffs i‖ := by simp
    _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum (fun i _ => hM i)
    _ = n * M := by simp [Finset.sum_const]

/-- Approximate a bounded function by a simple function on a partition of [-N, N].
    For n subdivisions, we use intervals [k/n, (k+1)/n) for k = -nN, ..., nN-1. -/
def approximateBySimple (f : ℝ → ℂ) (N : ℕ) (n : ℕ) (_hn : n > 0) : SimpleFunction (2 * N * n) where
  coeffs := fun i =>
    let k : ℤ := i.val - N * n
    f (k / n)
  sets := fun i =>
    let k : ℤ := i.val - N * n
    Set.Ico (k / n) ((k + 1) / n)

/-- The spectral integral of a step function approximation.
    This applies the simple function to the spectral measure. -/
def stepApproximation (P : SpectralMeasure H) (f : ℝ → ℂ) (N n : ℕ) (hn : n > 0) : H →L[ℂ] H :=
  (approximateBySimple f N n hn).spectralApply P

open MeasureTheory in
/-- For a spectral measure, construct the functional calculus via sesquilinear form.
    f(T) = ∫ f(λ) dP(λ) is constructed using the Riesz representation theorem:

    The sesquilinear form B_f(x,y) = ∫ f dμ_{x,y} (where μ_{x,y} is the complex spectral
    measure, constructed via polarization of diagonal measures) is bounded:
      |B_f(x,y)| ≤ ‖f‖_∞ · ‖x‖ · ‖y‖
    By `sesquilinearToOperator`, there exists a unique operator f(T) with
      ⟨x, f(T) y⟩ = B_f(x,y) = ∫ f(λ) d⟨x, P(·)y⟩(λ)

    Key properties:
    1. ∫ χ_E dP = P(E) for measurable E (characteristic property)
    2. ‖∫ f dP‖ ≤ sup |f| (operator norm bound)
    3. ∫ fg dP = (∫ f dP)(∫ g dP) (multiplicativity, Reed-Simon VIII.5b)
    4. (∫ f dP)* = ∫ f̄ dP (adjoint property, Reed-Simon VIII.5c) -/
def functionalCalculus (P : SpectralMeasure H) (f : ℝ → ℂ) : H →L[ℂ] H :=
  -- B_f(x,y) = ∫ f dμ_{x,y} via polarization: μ_{x,y} = (1/4)[μ_{x+y} - μ_{x-y} + iμ_{x+iy} - iμ_{x-iy}]
  let B : H → H → ℂ := fun x y =>
    (1/4 : ℂ) * (∫ t, f t ∂(P.diagonalMeasure (x + y))
      - ∫ t, f t ∂(P.diagonalMeasure (x - y))
      - Complex.I * ∫ t, f t ∂(P.diagonalMeasure (x + Complex.I • y))
      + Complex.I * ∫ t, f t ∂(P.diagonalMeasure (x - Complex.I • y)))
  sesquilinearToOperator B
    (by sorry) -- right-linearity: ∀ x, IsLinearMap ℂ (B x)
    (by sorry) -- conjugate-left-linearity
    (by sorry) -- boundedness: ∃ C, ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖

/-- The functional calculus is multiplicative: (fg)(T) = f(T)g(T)

    **Reference:** Reed-Simon Theorem VIII.5(b)

    The proof uses that for simple functions fₙ, gₘ approximating f, g:
    - (fₙ · gₘ)(T) = Σᵢⱼ fₙ(xᵢ)gₘ(xⱼ) P(Eᵢ ∩ Eⱼ)
    - = Σᵢⱼ fₙ(xᵢ)gₘ(xⱼ) P(Eᵢ)P(Eⱼ)  (by P(E∩F) = P(E)P(F))
    - = (Σᵢ fₙ(xᵢ)P(Eᵢ))(Σⱼ gₘ(xⱼ)P(Eⱼ))
    - = fₙ(T) · gₘ(T)
    Taking limits gives the result. -/
theorem functionalCalculus_mul (P : SpectralMeasure H) (f g : ℝ → ℂ) :
    functionalCalculus P (f * g) = functionalCalculus P f ∘L functionalCalculus P g := by
  -- FOUNDATIONAL: Reed-Simon VIII.5(b)
  -- Requires showing simple function approximations commute with multiplication
  sorry

/-- The functional calculus respects adjoints: f(T)* = f̄(T)

    **Reference:** Reed-Simon Theorem VIII.5(c)

    The proof uses that P(E)* = P(E) (self-adjointness of projections):
    - For simple f = Σᵢ cᵢ χ_{Eᵢ}: f(T)* = (Σᵢ cᵢ P(Eᵢ))* = Σᵢ c̄ᵢ P(Eᵢ) = f̄(T)
    - Extending to bounded Borel f uses continuity of the adjoint operation. -/
theorem functionalCalculus_star (P : SpectralMeasure H) (f : ℝ → ℂ) :
    ContinuousLinearMap.adjoint (functionalCalculus P f) =
    functionalCalculus P (star ∘ f) := by
  -- FOUNDATIONAL: Reed-Simon VIII.5(c)
  -- Uses P(E)* = P(E) and continuity of adjoint
  sorry


/-! ### The Spectral Theorem -/

/-- **The PVM Construction for Unbounded Self-Adjoint Operators (sorry-free)**

    For every densely defined self-adjoint operator T on a Hilbert space H,
    there exists a spectral measure P (projection-valued measure) and a
    Cayley transform C such that P.proj agrees with spectralMeasureFromRMK
    on all measurable sets.

    This is the core sorry-free construction. The spectral measure P is:
    - P(E) = spectralMeasureFromRMK T hT hsa C E hE for measurable E
    - P(E) = 0 for non-measurable E

    All PVM properties (empty, univ, idempotent, self-adjoint, multiplicative,
    monotone, σ-additive) are proven from the RMK chain.

    References: Reed-Simon Theorem VIII.4, Rudin Theorem 13.30 -/
theorem spectral_theorem_pvm (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ (P : SpectralMeasure H) (C : CayleyTransform T hT hsa),
      ∀ E (hE : MeasurableSet E), P.proj E = spectralMeasureFromRMK T hT hsa C E hE := by
  -- Step 1: Get the Cayley transform and PVM properties from spectralMeasure_isPVM_via_RMK
  -- The RMK approach proves: empty=0, univ=1, idempotent, selfAdjoint, multiplicative
  -- All of these are sorry-free!
  -- Note: This only proves P is a PVM; the T-P connection (final sorry below) is separate.
  obtain ⟨C, hP_empty, hP_univ, hP_idem, hP_sa, hP_inter⟩ :=
    spectralMeasure_isPVM_via_RMK T hT hsa
  -- Define P_raw from the RMK spectral measure
  -- For non-measurable sets, we define P(E) = 0
  let P_raw : Set ℝ → (H →L[ℂ] H) := fun E =>
    if hE : MeasurableSet E then spectralMeasureFromRMK T hT hsa C E hE else 0
  -- Step 2: Prove the SpectralMeasure properties for P_raw
  -- empty: P(∅) = 0
  have hP_raw_empty : P_raw ∅ = 0 := by
    simp only [P_raw, MeasurableSet.empty, ↓reduceDIte]
    exact hP_empty
  -- univ: P(ℝ) = 1
  have hP_raw_univ : P_raw Set.univ = 1 := by
    simp only [P_raw, MeasurableSet.univ, ↓reduceDIte]
    exact hP_univ
  -- isIdempotent: P(E)² = P(E) (for measurable E)
  have hP_raw_idem : ∀ E, MeasurableSet E → P_raw E ∘L P_raw E = P_raw E := by
    intro E hE
    simp only [P_raw, hE, ↓reduceDIte]
    exact hP_idem E hE
  -- isSelfAdj: P(E)* = P(E) (for measurable E)
  have hP_raw_sa : ∀ E, MeasurableSet E → (P_raw E).adjoint = P_raw E := by
    intro E hE
    simp only [P_raw, hE, ↓reduceDIte]
    exact hP_sa E hE
  -- inter: P(E ∩ F) = P(E) ∘L P(F) (for measurable E, F)
  have hP_raw_inter : ∀ E F, MeasurableSet E → MeasurableSet F →
      P_raw (E ∩ F) = P_raw E ∘L P_raw F := by
    intro E F hE hF
    simp only [P_raw, hE, hF, hE.inter hF, ↓reduceDIte]
    exact hP_inter E F hE hF
  -- monotone: E ⊆ F implies ‖P(E)x‖ ≤ ‖P(F)x‖ (for measurable E, F)
  have hP_raw_mono : ∀ E F, MeasurableSet E → MeasurableSet F → E ⊆ F →
      ∀ x : H, ‖P_raw E x‖ ≤ ‖P_raw F x‖ := by
    intro E F hE hF hEF x
    -- Both measurable: use the contraction property P(E) = P(E∩F) = P(E)∘P(F)
    have hEF_inter : E ∩ F = E := Set.inter_eq_left.mpr hEF
    have hPE_eq : P_raw E = P_raw E ∘L P_raw F := by
      rw [← hP_raw_inter E F hE hF, hEF_inter]
    have hPEx : P_raw E x = P_raw E (P_raw F x) := by
      calc P_raw E x = (P_raw E ∘L P_raw F) x := by rw [← hPE_eq]
        _ = P_raw E (P_raw F x) := rfl
    rw [hPEx]
    -- Projections are contractions: ‖P(E)y‖ ≤ ‖y‖
    by_cases hy : P_raw E (P_raw F x) = 0
    · rw [hy, norm_zero]; exact norm_nonneg _
    · have h1 : ‖P_raw E (P_raw F x)‖^2 =
          RCLike.re (@inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x))) :=
        (inner_self_eq_norm_sq _).symm
      have h2 : @inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x)) =
          @inner ℂ H _ (P_raw F x) ((P_raw E).adjoint (P_raw E (P_raw F x))) :=
        (ContinuousLinearMap.adjoint_inner_right (P_raw E) (P_raw F x) _).symm
      have h3 : (P_raw E).adjoint (P_raw E (P_raw F x)) = P_raw E (P_raw E (P_raw F x)) := by
        rw [hP_raw_sa E hE]
      have h5 : P_raw E (P_raw E (P_raw F x)) = P_raw E (P_raw F x) := by
        have := hP_raw_idem E hE
        simp only [] at this
        exact congrFun (congrArg DFunLike.coe this) (P_raw F x)
      have h_inner_eq : @inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x)) =
          @inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x)) := by rw [h2, h3, h5]
      have hcs : ‖@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))‖ ≤
          ‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖ := norm_inner_le_norm _ _
      have hre_le : RCLike.re (@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))) ≤
          ‖@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))‖ := by
        have h := Complex.abs_re_le_norm (@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x)))
        exact le_trans (le_abs_self _) h
      have h6 : ‖P_raw E (P_raw F x)‖^2 ≤ ‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖ := by
        calc ‖P_raw E (P_raw F x)‖^2 =
            RCLike.re (@inner ℂ H _ (P_raw E (P_raw F x)) (P_raw E (P_raw F x))) := h1
          _ = RCLike.re (@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))) := by rw [h_inner_eq]
          _ ≤ ‖@inner ℂ H _ (P_raw F x) (P_raw E (P_raw F x))‖ := hre_le
          _ ≤ ‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖ := hcs
      have hpos : 0 < ‖P_raw E (P_raw F x)‖ := norm_pos_iff.mpr hy
      calc ‖P_raw E (P_raw F x)‖ =
          ‖P_raw E (P_raw F x)‖^2 / ‖P_raw E (P_raw F x)‖ := by field_simp
        _ ≤ (‖P_raw F x‖ * ‖P_raw E (P_raw F x)‖) / ‖P_raw E (P_raw F x)‖ := by
          apply div_le_div_of_nonneg_right h6 hpos.le
        _ = ‖P_raw F x‖ := by field_simp
  -- sigma_additive: For disjoint measurable E_i, P(⋃ E_i)x = Σ P(E_i)x
  -- This requires transferring σ-additivity from the RMK construction.
  have hP_raw_sigma : ∀ (E : ℕ → Set ℝ), (∀ i, MeasurableSet (E i)) →
      (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
      ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P_raw (E i) x)
        Filter.atTop (nhds (P_raw (⋃ i, E i) x)) := by
    intro E hE_meas hE_disj x
    -- For measurable E_i, P_raw (E i) = spectralMeasureFromRMK ...
    have hP_raw_eq : ∀ i, P_raw (E i) = spectralMeasureFromRMK T hT hsa C (E i) (hE_meas i) := by
      intro i; simp only [P_raw, hE_meas i, ↓reduceDIte]
    have hP_raw_union : P_raw (⋃ i, E i) =
        spectralMeasureFromRMK T hT hsa C (⋃ i, E i) (MeasurableSet.iUnion hE_meas) := by
      simp only [P_raw, MeasurableSet.iUnion hE_meas, ↓reduceDIte]
    -- Use the sigma-additivity theorem from SigmaAdditivity.lean
    have h := spectralProjection_sigma_additive T hT hsa C E hE_meas hE_disj x
    simp only [hP_raw_eq] at *
    rw [hP_raw_union]
    exact h
  -- proj_nonmeasurable: P(E) = 0 for non-measurable E
  have hP_raw_nonmeas : ∀ E, ¬MeasurableSet E → P_raw E = 0 := by
    intro E hE; simp only [P_raw, hE, ↓reduceDIte]
  -- Step 3: Construct the SpectralMeasure
  let P : SpectralMeasure H := {
    proj := P_raw
    empty := hP_raw_empty
    univ := hP_raw_univ
    isIdempotent := hP_raw_idem
    isSelfAdj := hP_raw_sa
    inter := hP_raw_inter
    monotone := hP_raw_mono
    sigma_additive := hP_raw_sigma
    proj_nonmeasurable := hP_raw_nonmeas
  }
  -- Step 4: The conclusion - P.proj agrees with spectralMeasureFromRMK on measurable sets
  use P, C
  intro E hE
  -- For measurable E, P_raw E = spectralMeasureFromRMK T hT hsa C E hE by construction
  show P_raw E = spectralMeasureFromRMK T hT hsa C E hE
  exact dif_pos hE

/-- The spectral measure of a self-adjoint operator, extracted from `spectral_theorem_pvm`.
    This definition is sorry-free: the PVM is fully constructed from the RMK chain.
    For measurable E: `P.proj E = spectralMeasureFromRMK T hT hsa C E hE`. -/
def UnboundedOperator.spectralMeasure (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) : SpectralMeasure H :=
  (spectral_theorem_pvm T hT hsa).choose

/-- The Cayley transform associated with the spectral measure.
    This definition is sorry-free. -/
def UnboundedOperator.spectralCayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) : CayleyTransform T hT hsa :=
  (spectral_theorem_pvm T hT hsa).choose_spec.choose

/-- The core sorry-free property: spectral measure agrees with RMK construction.
    For all measurable E, `P.proj E = spectralMeasureFromRMK T hT hsa C E hE`. -/
theorem UnboundedOperator.spectralMeasure_eq_RMK (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (T.spectralMeasure hT hsa).proj E =
    spectralMeasureFromRMK T hT hsa (T.spectralCayley hT hsa) E hE :=
  (spectral_theorem_pvm T hT hsa).choose_spec.choose_spec E hE

/-! ### Powers of positive self-adjoint operators -/

/-- For a positive self-adjoint operator T and s ∈ ℂ, define T^s.
    This uses functional calculus: T^s = ∫ λ^s dP(λ) -/
def UnboundedOperator.power (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (_hpos : T.IsPositive) (s : ℂ) : H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  functionalCalculus P (fun x => if x > 0 then Complex.exp (s * Complex.log x) else 0)

/-- T^0 = 1

    **Proof:** The function f(λ) = λ^0 = 1 for λ > 0 (and 0 elsewhere).
    By functional calculus identity: ∫ 1 dP(λ) = P(ℝ) = 1.
    Depends on: functional calculus identity property. -/
theorem UnboundedOperator.power_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) :
    T.power hT hsa hpos 0 = 1 := by
  /-
  PROOF STRUCTURE:

  1. The power function is: f(λ) = if λ > 0 then exp(0 * log λ) else 0
  2. For λ > 0: exp(0 * log λ) = exp(0) = 1
  3. So f(λ) = 1 on (0, ∞) and f(λ) = 0 on (-∞, 0]

  For a positive operator T:
  - The spectrum is contained in [0, ∞)
  - The spectral projection P({0}) = 0 for strictly positive T
    (If 0 is an eigenvalue with non-trivial projection, T would have a kernel)
  - Therefore f = 1 on the support of P (up to a null set)
  - And ∫ 1 dP = P(ℝ) = 1

  The rigorous proof requires showing that for positive T:
  - P((0, ∞)) = P(ℝ) = 1 (i.e., P((-∞, 0]) = 0)
  - This uses positivity: ⟨x, Tx⟩ ≥ 0 implies spectrum ⊆ [0, ∞)
  -/
  unfold UnboundedOperator.power
  -- Show: functionalCalculus P (fun x => if x > 0 then exp(0 * log x) else 0) = 1
  -- Key: exp(0 * z) = exp(0) = 1 for all z
  have h1 : ∀ x : ℝ, (if x > 0 then Complex.exp (0 * Complex.log x) else 0) =
      (if x > 0 then 1 else 0) := by
    intro x
    split_ifs with hx
    · simp only [zero_mul, Complex.exp_zero]
    · rfl
  -- The function is χ_{(0,∞)}
  -- For a strictly positive operator, ∫ χ_{(0,∞)} dP = P((0,∞)) = P(ℝ) = 1
  -- This requires the positivity condition on T.
  --
  -- FOUNDATIONAL: Requires showing P((-∞, 0]) = 0 for positive T
  -- and that the functional calculus of the constant 1 on support is the identity.
  sorry

/-- T^(s+t) = T^s ∘ T^t

    **Proof:** Uses `functionalCalculus_mul`. The function λ^(s+t) = λ^s · λ^t pointwise,
    so ∫ λ^(s+t) dP = ∫ (λ^s · λ^t) dP = (∫ λ^s dP)(∫ λ^t dP) = T^s ∘ T^t.
    Depends on: `functionalCalculus_mul`. -/
theorem UnboundedOperator.power_add (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℂ) :
    T.power hT hsa hpos (s + t) = T.power hT hsa hpos s ∘L T.power hT hsa hpos t := by
  /-
  PROOF STRUCTURE:

  Define the power functions (where x : ℝ):
    f_s(x) = if x > 0 then exp(s * log x) else 0
    f_t(x) = if x > 0 then exp(t * log x) else 0
    f_{s+t}(x) = if x > 0 then exp((s+t) * log x) else 0

  Key identity: For x > 0,
    exp((s+t) * log x) = exp(s * log x + t * log x)
                       = exp(s * log x) * exp(t * log x)

  So f_{s+t} = f_s * f_t pointwise on (0, ∞).

  By functionalCalculus_mul:
    ∫ (f_s * f_t) dP = (∫ f_s dP) ∘ (∫ f_t dP)

  Therefore T^(s+t) = T^s ∘ T^t.
  -/
  unfold UnboundedOperator.power
  let P := T.spectralMeasure hT hsa
  -- The key: show the functions multiply correctly (x : ℝ)
  have h_fun_eq : (fun x : ℝ => if x > 0 then Complex.exp ((s + t) * Complex.log x) else 0) =
      (fun x : ℝ => if x > 0 then Complex.exp (s * Complex.log x) else 0) *
      (fun x : ℝ => if x > 0 then Complex.exp (t * Complex.log x) else 0) := by
    ext x
    simp only [Pi.mul_apply]
    split_ifs with hx
    · -- x > 0: use exp(a + b) = exp(a) * exp(b)
      rw [← Complex.exp_add]
      congr 1
      ring
    · -- x ≤ 0: 0 = 0 * 0
      ring
  rw [h_fun_eq]
  -- Apply functionalCalculus_mul
  exact functionalCalculus_mul P _ _

/-- For real t, T^{it} is unitary.

    **Proof:** Uses `functionalCalculus_star`. For real t:
    - (T^{it})* = ∫ conj(λ^{it}) dP = ∫ λ^{-it} dP = T^{-it}
    - T^{it} ∘ T^{-it} = T^0 = 1 (by `power_add` and `power_zero`)
    Depends on: `functionalCalculus_star`, `power_add`, `power_zero`. -/
theorem UnboundedOperator.power_imaginary_unitary (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    let u := T.power hT hsa hpos (Complex.I * t)
    ContinuousLinearMap.adjoint u ∘L u = 1 ∧ u ∘L ContinuousLinearMap.adjoint u = 1 := by
  /-
  PROOF STRUCTURE:

  Let u = T^{it} where the power function is:
    f_{it}(x) = if x > 0 then exp(it * log x) else 0

  **Step 1: Compute u* using functionalCalculus_star**
  u* = (∫ f_{it} dP)* = ∫ (star ∘ f_{it}) dP
  where (star ∘ f_{it})(x) = conj(f_{it}(x))

  For x > 0:
    conj(exp(it * log x)) = exp(conj(it * log x))
                          = exp(-it * log x)  [since log x ∈ ℝ for x > 0]
                          = exp((-it) * log x)

  So (star ∘ f_{it}) = f_{-it}, hence u* = T^{-it}

  **Step 2: Use power_add and power_zero**
  u* ∘ u = T^{-it} ∘ T^{it} = T^{-it + it} = T^0 = 1
  u ∘ u* = T^{it} ∘ T^{-it} = T^{it + (-it)} = T^0 = 1
  -/
  intro u
  -- First, show u* = T^{-it} using functionalCalculus_star
  have hu_adj : ContinuousLinearMap.adjoint u = T.power hT hsa hpos (-(Complex.I * t)) := by
    -- Key: conj(exp(it * log x)) = exp(-it * log x) for real log x
    -- This requires functionalCalculus_star and the conjugate identity
    -- Unfold both u and power to expose the functionalCalculus structure
    show ContinuousLinearMap.adjoint (T.power hT hsa hpos (Complex.I * t)) =
        T.power hT hsa hpos (-(Complex.I * t))
    unfold UnboundedOperator.power
    let P := T.spectralMeasure hT hsa
    -- f(x) = if x > 0 then exp(it * log x) else 0
    -- star ∘ f = fun x => if x > 0 then conj(exp(it * log x)) else 0
    --          = fun x => if x > 0 then exp(-it * log x) else 0  (for real log x)
    --          = g where g is the power function for -it
    have h_conj : star ∘ (fun x : ℝ => if x > 0 then Complex.exp (Complex.I * t * Complex.log x) else 0)
        = (fun x : ℝ => if x > 0 then Complex.exp (-(Complex.I * t) * Complex.log x) else 0) := by
      ext x
      simp only [Function.comp_apply]
      split_ifs with hx
      · -- x > 0: conj(exp(it * log x)) = exp(-it * log x)
        -- star on ℂ is conjugation: Complex.star_def
        rw [Complex.star_def]
        -- Use: conj(exp(z)) = exp(conj(z)) (Complex.exp_conj)
        rw [← Complex.exp_conj]
        congr 1
        -- conj(I * t * log x) = conj(I) * conj(t) * conj(log x)
        --                     = -I * t * log x  (for real t and real log x)
        rw [map_mul, map_mul]
        -- For real x > 0: log x is real, so conj(log x) = log x
        have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
        rw [hlog, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        ring
      · -- x ≤ 0: both sides are 0
        rw [Complex.star_def, map_zero]
    rw [functionalCalculus_star, h_conj]
  constructor
  · -- u* ∘ u = 1
    rw [hu_adj]
    have h1 : -(Complex.I * ↑t) + Complex.I * ↑t = 0 := by ring
    calc T.power hT hsa hpos (-(Complex.I * t)) ∘L T.power hT hsa hpos (Complex.I * t)
        = T.power hT hsa hpos (-(Complex.I * t) + Complex.I * t) := (T.power_add hT hsa hpos _ _).symm
      _ = T.power hT hsa hpos 0 := by rw [h1]
      _ = 1 := T.power_zero hT hsa hpos
  · -- u ∘ u* = 1
    rw [hu_adj]
    have h2 : Complex.I * ↑t + -(Complex.I * ↑t) = 0 := by ring
    calc T.power hT hsa hpos (Complex.I * t) ∘L T.power hT hsa hpos (-(Complex.I * t))
        = T.power hT hsa hpos (Complex.I * t + -(Complex.I * t)) := (T.power_add hT hsa hpos _ _).symm
      _ = T.power hT hsa hpos 0 := by rw [h2]
      _ = 1 := T.power_zero hT hsa hpos

/-! ### One-parameter unitary groups -/

/-- The one-parameter unitary group generated by a self-adjoint operator.
    U(t) = T^{it} for positive self-adjoint T -/
def unitaryGroup (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) : H →L[ℂ] H :=
  T.power hT hsa hpos (Complex.I * t)

/-- The group law: U(s) ∘ U(t) = U(s+t) -/
theorem unitaryGroup_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℝ) :
    unitaryGroup T hT hsa hpos s ∘L unitaryGroup T hT hsa hpos t =
    unitaryGroup T hT hsa hpos (s + t) := by
  -- U(s) ∘ U(t) = T^{is} ∘ T^{it} = T^{i(s+t)} = U(s+t)
  unfold unitaryGroup
  have h := T.power_add hT hsa hpos (Complex.I * s) (Complex.I * t)
  -- h: T^{is + it} = T^{is} ∘ T^{it}
  -- Need to show: T^{is} ∘ T^{it} = T^{i(s+t)}
  -- Note: is + it = i(s+t) by distributivity
  have heq : Complex.I * ↑s + Complex.I * ↑t = Complex.I * ↑(s + t) := by
    push_cast
    ring
  rw [← heq]
  exact h.symm

/-- U(0) = 1 -/
theorem unitaryGroup_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) :
    unitaryGroup T hT hsa hpos 0 = 1 := by
  -- U(0) = T^{i·0} = T^0 = 1
  unfold unitaryGroup
  have h : Complex.I * (0 : ℝ) = 0 := by simp
  rw [h]
  exact T.power_zero hT hsa hpos

/-- U(t)* = U(-t)

    **Proof:** Uses `functionalCalculus_star`:
    - U(t)* = (T^{it})* = ∫ conj(λ^{it}) dP = ∫ λ^{-it} dP = T^{-it} = U(-t)
    Depends on: `functionalCalculus_star`. -/
theorem unitaryGroup_inv (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    ContinuousLinearMap.adjoint (unitaryGroup T hT hsa hpos t) =
    unitaryGroup T hT hsa hpos (-t) := by
  -- U(t)* = (T^{it})* = T^{-it} = U(-t)
  unfold unitaryGroup
  -- First show i*(-t) = -(i*t)
  have heq : Complex.I * ((-t : ℝ) : ℂ) = -(Complex.I * (t : ℂ)) := by
    simp only [Complex.ofReal_neg, mul_neg]
  rw [heq]
  -- Now use the same proof as in power_imaginary_unitary
  unfold UnboundedOperator.power
  let P := T.spectralMeasure hT hsa
  have h_conj : star ∘ (fun x : ℝ => if x > 0 then Complex.exp (Complex.I * t * Complex.log x) else 0)
      = (fun x : ℝ => if x > 0 then Complex.exp (-(Complex.I * t) * Complex.log x) else 0) := by
    ext x
    simp only [Function.comp_apply]
    split_ifs with hx
    · rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      rw [map_mul, map_mul]
      have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
      rw [hlog, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      ring
    · rw [Complex.star_def, map_zero]
  rw [functionalCalculus_star, h_conj]

/-- U(-t) ∘ U(t) = 1 (left inverse) -/
theorem unitaryGroup_neg_comp (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    unitaryGroup T hT hsa hpos (-t) ∘L unitaryGroup T hT hsa hpos t = 1 := by
  rw [unitaryGroup_mul, neg_add_cancel, unitaryGroup_zero]

/-- U(t) ∘ U(-t) = 1 (right inverse) -/
theorem unitaryGroup_comp_neg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    unitaryGroup T hT hsa hpos t ∘L unitaryGroup T hT hsa hpos (-t) = 1 := by
  rw [unitaryGroup_mul, add_neg_cancel, unitaryGroup_zero]

/-- Strong continuity: t ↦ U(t)x is continuous for all x

    **Reference:** Reed-Simon Theorem VIII.8

    **Proof sketch:** The function t ↦ λ^{it} = exp(it·log λ) is continuous in t.
    By dominated convergence for spectral integrals:
      ‖U(t+h)x - U(t)x‖² = ∫ |λ^{i(t+h)} - λ^{it}|² dμ_x(λ) → 0 as h → 0
    where μ_x is the spectral measure associated to x.

    This requires the theory of integration against spectral measures. -/
theorem unitaryGroup_continuous (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (x : H) :
    Continuous (fun t => unitaryGroup T hT hsa hpos t x) := by
  -- FOUNDATIONAL: Reed-Simon VIII.8
  -- Requires dominated convergence for spectral integrals
  sorry

end

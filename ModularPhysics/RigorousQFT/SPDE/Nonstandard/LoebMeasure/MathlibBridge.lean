/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.LoebMeasure.LoebMeasurable
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.LoebMeasure.SigmaAdditivity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Mathlib Bridge: Loeb Measure as MeasureTheory.Measure

This file outlines the strategy for constructing the Loeb measure as an instance of
Mathlib's `MeasureTheory.Measure`.

## Goal

Bridge our nonstandard Loeb measure construction to Mathlib's measure theory, enabling:
1. Use of Mathlib's integration theorems (Fubini, dominated convergence)
2. Application of probability theory (expectation, variance, martingales)
3. Statement of Anderson's theorem: pushforward of Loeb measure = Wiener measure

## Current Infrastructure

Our existing construction works with **cardinalities** rather than sets:
- `InternalProbSpace` has `size : ℝ*` but no carrier type
- `InternalSubset` stores `card : ℝ*` as the cardinality
- `preLoebMeasure` computes `st(card/size)`

This abstracts away the underlying sample space, which is sufficient for
probability computations but not for constructing a Mathlib Measure directly.

## Strategy for Full Construction

To create a proper `MeasureTheory.Measure`, we need a concrete sample space.
For the hyperfinite random walk, this would be:

1. **Define the sample space**: For N steps, Ω_N = Fin N → Bool (coin flips)

2. **Define the hyperfinite sample space**: Use the ultraproduct construction
   Ω = Germ (hyperfilter ℕ) (fun n => Fin n → Bool)

3. **Define internal sets**: An internal set is a family A_n ⊆ Ω_n for each n,
   with coherence conditions from the ultrafilter

4. **Apply Carathéodory**: Extend preLoeb from internal algebra to σ-algebra

The key insight is that Mathlib's `OuterMeasure.toMeasure` already provides
Carathéodory extension—we just need to set up the types correctly.

## References

* Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
* Carathéodory, C. "Vorlesungen über reelle Funktionen" (1918)
* Mathlib documentation on MeasureTheory.OuterMeasure
-/

open scoped ENNReal
open MeasureTheory Set Hyperreal Filter

namespace SPDE.Nonstandard

/-! ## Concrete Sample Space for Hyperfinite Random Walk

For the Mathlib bridge, we work with the concrete hyperfinite coin flip space.
-/

/-- The sample space at level n: n coin flips -/
abbrev CoinFlips (n : ℕ) := Fin n → Bool

/-- An internal set in the hyperfinite probability space is a family of sets
    at each level, respecting the ultrafilter equivalence. -/
structure LevelwiseSet where
  /-- The set at each level -/
  sets : ∀ n : ℕ, Set (CoinFlips n)

/-- The cardinality at level n -/
noncomputable def LevelwiseSet.cardAtLevel (A : LevelwiseSet) (n : ℕ) : ℕ :=
  (A.sets n).toFinite.toFinset.card

/-- Two levelwise sets are equivalent if they agree on an ultrafilter-large set of levels -/
def LevelwiseSet.equiv (A B : LevelwiseSet) : Prop :=
  ∀ᶠ n in hyperfilter ℕ, A.sets n = B.sets n

/-- The hyperfinite cardinality as a hyperreal -/
noncomputable def LevelwiseSet.hyperCard (A : LevelwiseSet) : ℝ* :=
  Hyperreal.ofSeq (fun n => (A.cardAtLevel n : ℝ))

/-- The hyperfinite probability -/
noncomputable def LevelwiseSet.hyperProb (A : LevelwiseSet) : ℝ* :=
  Hyperreal.ofSeq (fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n)

/-- The pre-Loeb measure: standard part of the hyperfinite probability.
    We use Classical.propDecidable to handle the decidability issue. -/
noncomputable def LevelwiseSet.preLoeb (A : LevelwiseSet) : ℝ :=
  @dite ℝ (Hyperreal.Infinite A.hyperProb) (Classical.propDecidable _) (fun _ => 0) (fun _ => Hyperreal.st A.hyperProb)

/-! ## Properties of Pre-Loeb Measure -/

theorem LevelwiseSet.preLoeb_nonneg (A : LevelwiseSet) : 0 ≤ A.preLoeb := by
  unfold preLoeb
  by_cases h : Infinite A.hyperProb
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h]
    have hnn : 0 ≤ A.hyperProb := by
      unfold hyperProb ofSeq
      have hle : ∀ n, (0 : ℝ) ≤ (if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) := by
        intro n
        split_ifs
        · exact le_refl 0
        · apply div_nonneg
          · exact Nat.cast_nonneg _
          · exact pow_nonneg (by norm_num) _
      exact Germ.coe_le.mpr (Eventually.of_forall hle)
    have h0 : ¬Infinite (0 : ℝ*) := not_infinite_zero
    rw [← st_id_real 0]
    exact st_le_of_le h0 h hnn

theorem LevelwiseSet.preLoeb_le_one (A : LevelwiseSet) : A.preLoeb ≤ 1 := by
  unfold preLoeb
  by_cases h : Infinite A.hyperProb
  · simp only [dif_pos h]; linarith
  · simp only [dif_neg h]
    have hle : A.hyperProb ≤ 1 := by
      unfold hyperProb ofSeq
      have hle' : ∀ n, (if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) ≤ (1 : ℝ) := by
        intro n
        split_ifs with hn
        · linarith
        · apply div_le_one_of_le₀
          · have hcard : A.cardAtLevel n ≤ 2^n := by
              unfold cardAtLevel
              have hfin : (A.sets n).Finite := Set.toFinite _
              calc hfin.toFinset.card
                  ≤ (Finset.univ : Finset (CoinFlips n)).card := Finset.card_le_card (Finset.subset_univ _)
                _ = Fintype.card (CoinFlips n) := Finset.card_univ
                _ = Fintype.card (Fin n → Bool) := rfl
                _ = 2^n := by simp [Fintype.card_bool, Fintype.card_fin]
            calc (A.cardAtLevel n : ℝ)
                ≤ (2^n : ℕ) := Nat.cast_le.mpr hcard
              _ = 2^n := by norm_cast
          · exact pow_nonneg (by norm_num) _
      exact Germ.coe_le.mpr (Eventually.of_forall hle')
    have h1 : ¬Infinite (1 : ℝ*) := not_infinite_real 1
    rw [← st_id_real 1]
    exact st_le_of_le h h1 hle

/-- Empty set has pre-Loeb measure 0 -/
def LevelwiseSet.empty : LevelwiseSet where
  sets := fun _ => ∅

theorem LevelwiseSet.preLoeb_empty : LevelwiseSet.empty.preLoeb = 0 := by
  unfold preLoeb
  have hzero : LevelwiseSet.empty.hyperProb = 0 := by
    unfold hyperProb cardAtLevel ofSeq empty
    have h : (fun n => if n = 0 then (0 : ℝ) else
        (∅ : Set (CoinFlips n)).toFinite.toFinset.card / 2^n) = fun _ => 0 := by
      ext n
      split_ifs with hn
      · rfl
      · simp only [Set.toFinite_toFinset, Set.toFinset_empty, Finset.card_empty,
          Nat.cast_zero, zero_div]
    simp only [h]
    rfl
  rw [hzero]
  have h : ¬Infinite (0 : ℝ*) := not_infinite_zero
  simp only [dif_neg h]
  exact st_id_real 0

/-- Full set has pre-Loeb measure 1 -/
def LevelwiseSet.univ : LevelwiseSet where
  sets := fun _ => Set.univ

theorem LevelwiseSet.preLoeb_univ : LevelwiseSet.univ.preLoeb = 1 := by
  unfold preLoeb
  have hprob : LevelwiseSet.univ.hyperProb = 1 := by
    unfold hyperProb cardAtLevel ofSeq univ
    have h : (fun n => if n = 0 then (0 : ℝ) else
        (Set.univ : Set (CoinFlips n)).toFinite.toFinset.card / 2^n) =ᶠ[hyperfilter ℕ]
        (fun _ => (1 : ℝ)) := by
      -- Eventually n ≥ 1, and for n ≥ 1 the statement holds
      have hcofin : {n : ℕ | n ≠ 0} ∈ hyperfilter ℕ := by
        apply mem_hyperfilter_of_finite_compl
        simp only [Set.compl_setOf, ne_eq, Decidable.not_not]
        exact Set.finite_singleton 0
      apply Eventually.mono hcofin
      intro n hn
      simp only [ne_eq] at hn
      simp only [if_neg hn]
      have hcard : (Set.univ : Set (CoinFlips n)).toFinite.toFinset.card = 2^n := by
        simp only [Set.Finite.toFinset_univ, Finset.card_univ]
        simp [Fintype.card_bool, Fintype.card_fin]
      simp only [hcard, Nat.cast_pow, Nat.cast_ofNat]
      have hpos : (2 : ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hpos]
    exact Germ.coe_eq.mpr h
  rw [hprob]
  have h1 : ¬Infinite (1 : ℝ*) := not_infinite_real 1
  simp only [dif_neg h1]
  exact st_id_real 1

/-! ## Finite Additivity

The pre-Loeb measure is finitely additive on disjoint levelwise sets.
-/

/-- Disjoint levelwise sets -/
def LevelwiseSet.AreDisjoint (A B : LevelwiseSet) : Prop :=
  ∀ n, Disjoint (A.sets n) (B.sets n)

/-- Union of levelwise sets -/
def LevelwiseSet.union (A B : LevelwiseSet) : LevelwiseSet where
  sets := fun n => A.sets n ∪ B.sets n

/-- For disjoint sets at each level, the union cardinality equals the sum -/
theorem LevelwiseSet.cardAtLevel_union_disjoint (A B : LevelwiseSet) (h : A.AreDisjoint B) (n : ℕ) :
    (A.union B).cardAtLevel n = A.cardAtLevel n + B.cardAtLevel n := by
  unfold cardAtLevel union
  simp only
  have hdisj : Disjoint (A.sets n) (B.sets n) := h n
  -- The finite toFinsets of disjoint sets have disjoint toFinsets
  have hfinA : (A.sets n).Finite := Set.toFinite _
  have hfinB : (B.sets n).Finite := Set.toFinite _
  have hfinU : (A.sets n ∪ B.sets n).Finite := Set.toFinite _
  -- Convert to Finset disjointness
  have hfindisj : Disjoint hfinA.toFinset hfinB.toFinset := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Set.Finite.mem_toFinset] at ha hb
    intro heq
    rw [heq] at ha
    exact Set.disjoint_iff.mp hdisj ⟨ha, hb⟩
  -- The union toFinset equals the disjoint union of toFinsets
  have hunion : hfinU.toFinset = hfinA.toFinset ∪ hfinB.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_union]
  rw [hunion, Finset.card_union_of_disjoint hfindisj]

/-- The hyperfinite probability of disjoint union equals the sum -/
theorem LevelwiseSet.hyperProb_add_disjoint (A B : LevelwiseSet) (h : A.AreDisjoint B) :
    (A.union B).hyperProb = A.hyperProb + B.hyperProb := by
  unfold hyperProb ofSeq
  have hadd : (fun n => if n = 0 then (0 : ℝ) else ((A.union B).cardAtLevel n : ℝ) / 2^n) =
              (fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) +
              (fun n => if n = 0 then 0 else (B.cardAtLevel n : ℝ) / 2^n) := by
    ext n
    simp only [Pi.add_apply]
    split_ifs with hn
    · ring
    · rw [cardAtLevel_union_disjoint A B h n]
      simp only [Nat.cast_add, add_div]
  rw [hadd, Germ.coe_add]

theorem LevelwiseSet.preLoeb_add_disjoint (A B : LevelwiseSet) (h : A.AreDisjoint B) :
    (A.union B).preLoeb = A.preLoeb + B.preLoeb := by
  unfold preLoeb
  rw [hyperProb_add_disjoint A B h]
  -- Case analysis on finiteness
  -- Helper: hyperProb is bounded between 0 and 1, hence not infinite
  have hyperProb_not_infinite : ∀ X : LevelwiseSet, ¬Infinite X.hyperProb := by
    intro X
    have hle : X.hyperProb ≤ 1 := by
      unfold hyperProb ofSeq
      have hle' : ∀ n, (if n = 0 then 0 else (X.cardAtLevel n : ℝ) / 2^n) ≤ (1 : ℝ) := by
        intro n
        split_ifs with hn
        · linarith
        · apply div_le_one_of_le₀
          · have hcard : X.cardAtLevel n ≤ 2^n := by
              unfold cardAtLevel
              have hfin : (X.sets n).Finite := Set.toFinite _
              calc hfin.toFinset.card
                  ≤ (Finset.univ : Finset (CoinFlips n)).card := Finset.card_le_card (Finset.subset_univ _)
                _ = Fintype.card (CoinFlips n) := Finset.card_univ
                _ = 2^n := by simp [Fintype.card_bool, Fintype.card_fin]
            calc (X.cardAtLevel n : ℝ) ≤ (2^n : ℕ) := Nat.cast_le.mpr hcard
              _ = 2^n := by norm_cast
          · exact pow_nonneg (by norm_num) _
      exact Germ.coe_le.mpr (Eventually.of_forall hle')
    have hnn : 0 ≤ X.hyperProb := by
      unfold hyperProb ofSeq
      have hle' : ∀ n, (0 : ℝ) ≤ (if n = 0 then 0 else (X.cardAtLevel n : ℝ) / 2^n) := by
        intro n
        split_ifs
        · linarith
        · apply div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
      exact Germ.coe_le.mpr (Eventually.of_forall hle')
    -- If 0 ≤ x ≤ 1, then x is not infinite
    rw [not_infinite_iff_exist_lt_gt]
    refine ⟨-1, 2, ?_, ?_⟩
    · calc (-1 : ℝ*) < 0 := by norm_num
        _ ≤ X.hyperProb := hnn
    · calc X.hyperProb ≤ 1 := hle
        _ < 2 := by norm_num
  by_cases hA : Infinite A.hyperProb
  · exact absurd hA (hyperProb_not_infinite A)
  · by_cases hB : Infinite B.hyperProb
    · exact absurd hB (hyperProb_not_infinite B)
    · -- Both finite, so use st_add
      have hAB : ¬Infinite (A.hyperProb + B.hyperProb) := not_infinite_add hA hB
      simp only [dif_neg hA, dif_neg hB, dif_neg hAB]
      exact st_add hA hB

/-! ## Toward Carathéodory Extension

For a full Mathlib measure, we need to:
1. Define the outer measure via countable covers
2. Show internal sets satisfy the Carathéodory condition
3. Verify the resulting measure agrees with pre-Loeb on internal sets

The key theorem that enables this is `DecreasingConcreteEvents.sigma_additivity`
from SigmaAdditivity.lean, which shows that for decreasing sequences with
empty intersection, the pre-Loeb measures converge to 0.
-/

/-- The Loeb outer measure on levelwise sets.
    μ*(E) = inf { Σ preLoeb(A_i) : E ⊆ ⋃ A_i, A_i internal } -/
noncomputable def loebOuterMeasureValue (E : LevelwiseSet) : ℝ≥0∞ :=
  ⨅ (cover : ℕ → LevelwiseSet) (_ : ∀ m, ∀ᶠ k in hyperfilter ℕ,
      E.sets k ⊆ ⋃ i ∈ Finset.range (m + 1), (cover i).sets k),
    ∑' i, ENNReal.ofReal (cover i).preLoeb

/-! ## Summary and Next Steps

This file provides the conceptual framework for bridging to Mathlib's measure theory.

**What's Done:**
- `LevelwiseSet`: Concrete representation of internal sets as families indexed by ℕ
- `hyperProb`, `preLoeb`: Hyperfinite probability and its standard part
- Basic properties: nonnegativity, boundedness, empty/full set measures
- `loebOuterMeasureValue`: Outer measure definition via covers

**What Needs Work:**
- Prove `preLoeb_add_disjoint` (finite additivity)
- Show the outer measure is indeed an `OuterMeasure`
- Verify Carathéodory condition for internal sets
- Construct the Mathlib `Measure` instance

**Key Insight:**
The hard work is already done in `SigmaAdditivity.lean`. The bridge to Mathlib
is mostly about setting up the right type-theoretic structures to apply the
existing `OuterMeasure.toMeasure` construction.

Once complete, Anderson's theorem can be stated as:
```
theorem anderson :
    Measure.map (standardPart : HyperfiniteWalk → C([0,1], ℝ)) loebMeasure = wienerMeasure
```
-/

end SPDE.Nonstandard

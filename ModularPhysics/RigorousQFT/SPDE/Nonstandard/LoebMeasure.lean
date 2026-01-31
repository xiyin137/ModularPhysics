/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.Ultrafilter.Basic
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Foundation.Hypernatural
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Foundation.HyperfiniteSum
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Foundation.InternalMembership
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Foundation.Saturation

/-!
# Loeb Measure Construction

This file develops the Loeb measure construction, which converts internal
(hyperfinite) probability measures into genuine σ-additive measures.

## The Key Insight

In the hyperfinite world, probability is just counting:
- Sample space Ω has N elements (N hyperfinite, possibly infinite)
- P(A) = |A|/N for internal subsets A

This is a finitely additive measure on the internal algebra.
Loeb's construction extends this to a σ-additive measure on a σ-algebra.

## Current State

This file provides:
- Pre-Loeb measure (standard part of internal probability)
- Basic properties: non-negativity, finite additivity, monotonicity
- Connection to coin flip spaces and hyperfinite random walks

The saturation infrastructure is now available in `Foundation.Saturation`,
enabling σ-additivity arguments. See the section "Saturation and σ-Additivity"
below for details.

## Remaining Work

A complete formalization still requires:
- Carathéodory extension for the σ-algebra
- Full definition of Loeb measurability for external sets
- Anderson's theorem (pushforward = Wiener measure)

## References

* Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
* Anderson, R. M. "A nonstandard representation for Brownian motion" (1976)
* Cutland, N. "Loeb Measures in Practice: Recent Advances"
-/

open MeasureTheory Hyperreal Classical Ultrafilter

namespace SPDE.Nonstandard

/-! ## Internal Probability Spaces

An internal probability space is a hyperfinite set with counting measure.
-/

/-- An internal (hyperfinite) probability space.
    This is a set of size N with uniform probability 1/N on each element. -/
structure InternalProbSpace where
  /-- The (hyperfinite) size of the sample space -/
  size : ℝ*
  /-- The size is positive -/
  size_pos : 0 < size

namespace InternalProbSpace

/-- The internal probability of a subset with given cardinality -/
noncomputable def prob (Ω : InternalProbSpace) (card : ℝ*) : ℝ* :=
  card / Ω.size

/-- The whole space has probability 1 -/
theorem prob_whole (Ω : InternalProbSpace) : Ω.prob Ω.size = 1 := by
  unfold prob
  exact div_self (ne_of_gt Ω.size_pos)

/-- The empty set has probability 0 -/
theorem prob_empty (Ω : InternalProbSpace) : Ω.prob 0 = 0 := by
  simp [prob]

/-- The internal probability is non-negative for non-negative cardinalities -/
theorem prob_nonneg (Ω : InternalProbSpace) (card : ℝ*) (hcard : 0 ≤ card) :
    0 ≤ Ω.prob card :=
  div_nonneg hcard (le_of_lt Ω.size_pos)

/-- The internal probability is at most 1 for valid cardinalities -/
theorem prob_le_one (Ω : InternalProbSpace) (card : ℝ*) (hcard : card ≤ Ω.size) :
    Ω.prob card ≤ 1 := by
  unfold prob
  rw [div_le_one (Ω.size_pos)]
  exact hcard

/-- Probability is additive: P(A ∪ B) = P(A) + P(B) for disjoint A, B -/
theorem prob_add (Ω : InternalProbSpace) (card₁ card₂ : ℝ*) :
    Ω.prob (card₁ + card₂) = Ω.prob card₁ + Ω.prob card₂ := by
  unfold prob
  rw [add_div]

/-- Probability of the complement: P(Ω \ A) = 1 - P(A) -/
theorem prob_compl (Ω : InternalProbSpace) (card : ℝ*) (_hcard : card ≤ Ω.size) :
    Ω.prob (Ω.size - card) = 1 - Ω.prob card := by
  unfold prob
  rw [sub_div, div_self (ne_of_gt Ω.size_pos)]

/-- Probability is monotone: if |A| ≤ |B| then P(A) ≤ P(B) -/
theorem prob_mono (Ω : InternalProbSpace) (card₁ card₂ : ℝ*) (h : card₁ ≤ card₂) :
    Ω.prob card₁ ≤ Ω.prob card₂ :=
  div_le_div_of_nonneg_right h (le_of_lt Ω.size_pos)

/-- Probability difference: P(A) - P(B) = P(|A| - |B|) -/
theorem prob_sub (Ω : InternalProbSpace) (card₁ card₂ : ℝ*) :
    Ω.prob card₁ - Ω.prob card₂ = Ω.prob (card₁ - card₂) := by
  unfold prob
  rw [sub_div]

/-- Probability scales linearly with cardinality -/
theorem prob_smul (Ω : InternalProbSpace) (c : ℝ*) (card : ℝ*) :
    Ω.prob (c * card) = c * Ω.prob card := by
  unfold prob
  rw [mul_div_assoc]

/-- The probability is finite when cardinality is bounded -/
theorem prob_finite (Ω : InternalProbSpace) (card : ℝ*) (hcard₁ : 0 ≤ card)
    (hcard₂ : card ≤ Ω.size) (_hsize : ¬Infinite Ω.size) : ¬Infinite (Ω.prob card) := by
  intro hinf
  have h1 : Ω.prob card ≤ 1 := prob_le_one Ω card hcard₂
  have h2 : 0 ≤ Ω.prob card := prob_nonneg Ω card hcard₁
  -- A value in [0, 1] cannot be infinite
  cases hinf with
  | inl hpos =>
    -- Positive infinite: prob > r for all real r, contradicts prob ≤ 1
    have : (1 : ℝ*) < Ω.prob card := hpos 1
    exact absurd h1 (not_le.mpr this)
  | inr hneg =>
    -- Negative infinite: prob < r for all real r, contradicts 0 ≤ prob
    have : Ω.prob card < (0 : ℝ*) := hneg 0
    exact absurd h2 (not_le.mpr this)

end InternalProbSpace

/-! ## Pre-Loeb Measure

The pre-Loeb measure takes standard parts of internal probabilities.
-/

/-- The pre-Loeb measure: standard part of internal probability.
    For probabilities in [0,1], this is always well-defined (not infinite). -/
noncomputable def preLoebMeasure (Ω : InternalProbSpace) (card : ℝ*) : ℝ :=
  if _ : ¬Infinite (Ω.prob card) then st (Ω.prob card) else 0

/-- When the probability is finite (between 0 and 1), preLoebMeasure equals st -/
theorem preLoebMeasure_eq_st (Ω : InternalProbSpace) (card : ℝ*)
    (hfinite : ¬Infinite (Ω.prob card)) :
    preLoebMeasure Ω card = st (Ω.prob card) := by
  simp [preLoebMeasure, hfinite]

/-- Pre-Loeb measure of empty set is 0 -/
theorem preLoebMeasure_empty (Ω : InternalProbSpace) :
    preLoebMeasure Ω 0 = 0 := by
  have h : Ω.prob 0 = 0 := Ω.prob_empty
  have hfin : ¬Infinite (Ω.prob 0) := by rw [h]; exact not_infinite_zero
  rw [preLoebMeasure, dif_pos hfin, h]
  exact st_id_real 0

/-- Pre-Loeb measure of whole space is 1 -/
theorem preLoebMeasure_whole (Ω : InternalProbSpace) :
    preLoebMeasure Ω Ω.size = 1 := by
  have h : Ω.prob Ω.size = 1 := Ω.prob_whole
  have hfin : ¬Infinite (Ω.prob Ω.size) := by rw [h]; exact not_infinite_real 1
  rw [preLoebMeasure, dif_pos hfin, h]
  exact st_id_real 1

/-- Pre-Loeb measure is non-negative when internal prob is in [0, 1] -/
theorem preLoebMeasure_nonneg (Ω : InternalProbSpace) (card : ℝ*)
    (hcard₁ : 0 ≤ card) (hfin : ¬Infinite (Ω.prob card)) :
    0 ≤ preLoebMeasure Ω card := by
  rw [preLoebMeasure_eq_st Ω card hfin]
  have hprob : 0 ≤ Ω.prob card := Ω.prob_nonneg card hcard₁
  have h0 : ¬Infinite (0 : ℝ*) := not_infinite_zero
  rw [← st_id_real 0]
  exact st_le_of_le h0 hfin hprob

/-- Pre-Loeb measure is at most 1 when cardinality is bounded -/
theorem preLoebMeasure_le_one (Ω : InternalProbSpace) (card : ℝ*)
    (hcard : card ≤ Ω.size) (hfin : ¬Infinite (Ω.prob card)) :
    preLoebMeasure Ω card ≤ 1 := by
  rw [preLoebMeasure_eq_st Ω card hfin]
  have hprob : Ω.prob card ≤ 1 := Ω.prob_le_one card hcard
  have h1 : ¬Infinite (1 : ℝ*) := not_infinite_real 1
  rw [← st_id_real 1]
  exact st_le_of_le hfin h1 hprob

/-- Pre-Loeb measure is additive for finite probabilities -/
theorem preLoebMeasure_add (Ω : InternalProbSpace) (card₁ card₂ : ℝ*)
    (hfin₁ : ¬Infinite (Ω.prob card₁)) (hfin₂ : ¬Infinite (Ω.prob card₂))
    (_hfin : ¬Infinite (Ω.prob (card₁ + card₂))) :
    preLoebMeasure Ω (card₁ + card₂) = preLoebMeasure Ω card₁ + preLoebMeasure Ω card₂ := by
  -- Use that sum of non-infinite values is non-infinite
  have hfin_sum : ¬Infinite (Ω.prob card₁ + Ω.prob card₂) := by
    rw [← Ω.prob_add]
    exact _hfin
  rw [preLoebMeasure_eq_st Ω card₁ hfin₁,
      preLoebMeasure_eq_st Ω card₂ hfin₂,
      preLoebMeasure, dif_pos (by rw [Ω.prob_add]; exact hfin_sum)]
  rw [Ω.prob_add]
  -- st(a + b) = st(a) + st(b) when both are finite
  have h1 : IsSt (Ω.prob card₁) (st (Ω.prob card₁)) := isSt_st' hfin₁
  have h2 : IsSt (Ω.prob card₂) (st (Ω.prob card₂)) := isSt_st' hfin₂
  have h3 : IsSt (Ω.prob card₁ + Ω.prob card₂) (st (Ω.prob card₁) + st (Ω.prob card₂)) :=
    h1.add h2
  exact h3.st_eq

/-! ## σ-Additivity via Saturation

The key to proving σ-additivity of Loeb measure is the following lemma:
For a decreasing sequence of internal sets Aₙ with μ(Aₙ) ≥ ε > 0 for all n,
the intersection ⋂ₙ Aₙ is nonempty (by saturation).

Contrapositive: If ⋂ₙ Aₙ = ∅, then μ(Aₙ) → 0.

This gives σ-additivity from above (continuity at ∅), which together with
finite additivity implies full σ-additivity.

The saturation theorem is in `Foundation.Saturation.countable_saturation_standard`.
-/

/-- A decreasing sequence of internal sets (for the saturation argument).
    This represents Aₙ ⊇ Aₙ₊₁ for all n. -/
structure DecreasingInternalFamily where
  /-- The sequence of internal sets -/
  sets : ℕ → Foundation.InternalSet
  /-- Decreasing: Aₙ ⊇ Aₙ₊₁ at each level -/
  decreasing : ∀ (n m k : ℕ), n ≤ m → (sets m).sets k ⊆ (sets n).sets k

/-- Convert a decreasing family to a CountableInternalFamily for saturation. -/
def DecreasingInternalFamily.toCountableFamily (F : DecreasingInternalFamily) :
    Foundation.CountableInternalFamily where
  family := F.sets

/-- The key lemma for σ-additivity: if all sets in a decreasing family are
    "nonempty at level n" (for the saturation argument), then the intersection
    is nonempty.

    This follows from `countable_saturation_standard` applied to the family.
    The decreasing property ensures that level-n witnesses transfer correctly. -/
theorem decreasing_family_saturation (F : DecreasingInternalFamily)
    (hFIP : F.toCountableFamily.HasStandardFIP) :
    ∃ x : ℝ*, ∀ n : ℕ, (F.sets n).mem x :=
  Foundation.countable_saturation_standard F.toCountableFamily hFIP

/-! ### Application to Loeb Measure σ-Additivity

For the actual σ-additivity proof, we would need to:
1. Define internal sets Aₙ with μ(Aₙ) ≥ ε
2. Show these form a family with HasStandardFIP
3. Apply saturation to get a point in ⋂ Aₙ
4. Derive contradiction if ⋂ Aₙ was assumed empty

The details depend on how internal sets are represented. The saturation
infrastructure is ready; the remaining work is in the measure-theoretic setup.
-/

/-! ## The Coin Flip Space

The canonical example: N fair coin flips. Sample space has 2^N elements.
-/

/-- Hyperreal exponentiation: 2^n for sequence-defined hyperreals.
    For a hyperreal N = ofSeq f, we define 2^N = ofSeq (2^(f n)).
    This requires N to be a hypernatural (from a sequence of naturals). -/
noncomputable def hyperPow2Seq (f : ℕ → ℕ) : ℝ* :=
  ofSeq (fun n => (2 : ℝ)^(f n))

/-- 2^N is positive for any sequence -/
theorem hyperPow2Seq_pos (f : ℕ → ℕ) : 0 < hyperPow2Seq f := by
  have h : ∀ n, (0 : ℝ) < 2^(f n) := fun n => pow_pos (by norm_num : (0 : ℝ) < 2) (f n)
  exact ofSeq_lt_ofSeq.mpr (Filter.Eventually.of_forall h)

/-- 2^N is infinite when N → ∞.
    The key idea: 2^(f n) → ∞ as f n → ∞, so 2^(f n) > M for almost all n. -/
theorem hyperPow2Seq_infinite (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Infinite (hyperPow2Seq f) := by
  left  -- Show InfinitePos
  intro M
  -- Find N₀ such that for n ≥ N₀, f(n) is large enough that 2^(f(n)) > M
  -- This uses that f → ∞ and 2^k → ∞ as k → ∞
  have hev : ∀ᶠ n in Filter.atTop, M < (2 : ℝ)^(f n) := by
    -- 2^(f n) → ∞ as n → ∞ when f n → ∞
    have h2pow : Filter.Tendsto (fun n => (2 : ℝ)^(f n)) Filter.atTop Filter.atTop := by
      -- Composition: (2^·) ∘ f tends to ∞ since f → ∞ and 2^· : ℕ → ℝ → ∞
      have hbase : Filter.Tendsto (fun k : ℕ => (2 : ℝ)^k) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      exact hbase.comp hf
    exact h2pow.eventually_gt_atTop M
  -- The set {n | M < 2^(f n)} is cofinite (contains a tail), hence in hyperfilter
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  have hcofin : {n | M < (2 : ℝ)^(f n)} ∈ Filter.cofinite := by
    rw [Filter.mem_cofinite]
    refine (Set.finite_lt_nat N₀).subset ?_
    intro n hn
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hn
    simp only [Set.mem_setOf_eq]
    by_contra hge
    push_neg at hge
    exact not_lt.mpr hn (hN₀ n hge)
  -- hyperfilter extends cofinite for infinite types
  -- hyperfilter_le_cofinite : ↑(hyperfilter α) ≤ cofinite
  -- So if s ∈ cofinite, then s ∈ hyperfilter
  have hmem : {n | M < (2 : ℝ)^(f n)} ∈ (Filter.hyperfilter ℕ : Filter ℕ) := by
    -- Use that hyperfilter ≤ cofinite
    exact Filter.hyperfilter_le_cofinite hcofin
  exact ofSeq_lt_ofSeq.mpr hmem

/-- 2^N is infinite when N is an infinite hypernatural.
    This version uses ultrafilter membership directly, avoiding pointwise convergence. -/
theorem hyperPow2Seq_infinite_of_hypernat (N : Foundation.Hypernat)
    (hNinf : Foundation.Hypernat.Infinite N) : Infinite (hyperPow2Seq N.toSeq) := by
  left  -- Show InfinitePos
  intro M
  -- For any M, we need {n | M < 2^(N.toSeq n)} ∈ hyperfilter
  -- Find b such that 2^b > M, then use that {n | b < N.toSeq n} ∈ hyperfilter
  have harch : ∃ b : ℕ, M < (2 : ℝ)^b := by
    have htend : Filter.Tendsto (fun k : ℕ => (2 : ℝ)^k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    exact (htend.eventually_gt_atTop M).exists
  obtain ⟨b, hb⟩ := harch
  -- For n with N.toSeq n > b, we have 2^(N.toSeq n) > 2^b > M
  have hev_gt : ∀ᶠ n in Filter.hyperfilter ℕ, b < N.toSeq n :=
    Foundation.Hypernat.toSeq_eventually_gt_of_infinite N hNinf b
  have hmem : ∀ᶠ n in Filter.hyperfilter ℕ, M < (2 : ℝ)^(N.toSeq n) := by
    apply hev_gt.mono
    intro n hn
    -- Show M < 2^b < 2^(N.toSeq n)
    have hpow_mono : (2 : ℝ)^b < (2 : ℝ)^(N.toSeq n) := by
      have h2gt1 : (1 : ℝ) < 2 := by norm_num
      have h2pos : (0 : ℝ) < 2 := by norm_num
      -- 2^k is strictly increasing for k : ℕ when base > 1
      have hbase : ∀ k : ℕ, (2 : ℝ)^k < (2 : ℝ)^(k+1) := by
        intro k
        calc (2 : ℝ)^k < (2 : ℝ)^k * 2 := by nlinarith [pow_pos h2pos k]
          _ = (2 : ℝ)^(k + 1) := by ring
      -- Apply strict monotonicity
      have hmono : StrictMono (fun k : ℕ => (2 : ℝ)^k) :=
        strictMono_nat_of_lt_succ hbase
      exact hmono hn
    linarith
  exact ofSeq_lt_ofSeq.mpr hmem

/-- The internal probability space of N coin flips.
    Uses hyperPow2Seq to properly compute 2^N from the underlying sequence. -/
noncomputable def coinFlipSpace (f : ℕ → ℕ) : InternalProbSpace where
  size := hyperPow2Seq f
  size_pos := hyperPow2Seq_pos f

/-- Alternative: coin flip space from a hypernatural -/
noncomputable def coinFlipSpaceHypernat (N : Foundation.Hypernat) : InternalProbSpace where
  size := hyperPow2Seq N.toSeq
  size_pos := hyperPow2Seq_pos N.toSeq

/-! ## Loeb σ-algebra and Measure

The full Loeb construction extends the pre-measure to a σ-algebra.
A set A is Loeb measurable if for every ε > 0, there exist internal sets
B ⊆ A ⊆ C with μ(C) - μ(B) < ε.

**Note**: A rigorous development requires internal set theory, which
distinguishes between internal sets (those definable in the nonstandard
model) and external sets. This is beyond what mathlib's Hyperreal provides.
-/

/-! ## Loeb Measure: What We Can and Cannot Prove

The Loeb measure construction converts internal (hyperfinite) finitely additive
measures into genuine σ-additive measures. The key insight is that the standard
part operation, when applied to internal probabilities, yields a countably
additive measure on a suitable σ-algebra.

### What's Proven Here

1. **Pre-Loeb measure**: We define `preLoebMeasure` as the standard part of
   internal probabilities. This is well-defined for probabilities in [0,1].

2. **Basic properties**: Pre-Loeb measure is non-negative, bounded by 1,
   and finitely additive (proven above).

3. **Internal probability spaces**: Proper definitions with 2^N size for
   coin flip spaces.

4. **Saturation**: The ℵ₁-saturation theorem is now available in
   `Foundation.Saturation`. This enables σ-additivity proofs.

### Saturation and σ-Additivity

The key use of saturation is to prove σ-additivity from above (continuity at ∅):
If {Aₙ} is a decreasing sequence of internal sets with ⋂ₙ Aₙ = ∅,
then μ_L(Aₙ) → 0.

**Proof sketch using saturation**:
Suppose μ(Aₙ) ≥ ε > 0 for all n (where ε is standard positive).
Consider the internal sets Aₙ ∩ [probability ≥ ε/2].
These form a countable family with the finite intersection property
(since μ(Aₙ) ≥ ε > 0 implies Aₙ is nonempty).
By saturation, ⋂ₙ Aₙ ≠ ∅, contradicting the assumption.

The saturation theorem `countable_saturation_standard` in `Foundation.Saturation`
provides the infrastructure for such arguments.

### What Still Requires Work

1. **Carathéodory extension**: Building a σ-algebra from the internal algebra.
   This is standard measure theory but requires careful bookkeeping.

2. **Full Loeb measurability**: Defining when an external set is Loeb measurable.

3. **Anderson's theorem**: Proving the pushforward equals Wiener measure.

### References

- Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
- Goldblatt, R. "Lectures on the Hyperreals", Chapter 16
- Cutland, N. "Loeb Measures in Practice"
-/

/-! ## Connection to Hyperfinite Random Walks

The hyperfinite random walk lives on a probability space where:
- Sample space = all sequences of N coin flips = {-1, +1}^N
- Size = 2^N (number of such sequences)
- Each path has probability 1/2^N

Key observation: The random walk W_k = √dt · (X₁ + ... + Xₖ) depends only
on the first k coin flips. Events like "W_k > 0" are determined by counting
how many of the 2^N paths satisfy this condition.
-/

/-- The probability space underlying a hyperfinite random walk with N steps.
    The sample space is {-1, +1}^N with 2^N elements. -/
noncomputable def walkProbSpace (N : Foundation.Hypernat) : InternalProbSpace :=
  coinFlipSpaceHypernat N

/-- Each individual path has probability 1/2^N -/
theorem singlePath_prob (N : Foundation.Hypernat) :
    (walkProbSpace N).prob 1 = 1 / (walkProbSpace N).size := by
  unfold walkProbSpace coinFlipSpaceHypernat InternalProbSpace.prob
  simp only [one_div]

/-- When N is infinite, individual paths have infinitesimal probability -/
theorem singlePath_infinitesimal (N : Foundation.Hypernat) (hNinf : Foundation.Hypernat.Infinite N) :
    Infinitesimal ((walkProbSpace N).prob 1) := by
  rw [singlePath_prob N, one_div]
  -- 1/2^N is infinitesimal when N is infinite
  have hsize : Infinite (walkProbSpace N).size := by
    unfold walkProbSpace coinFlipSpaceHypernat
    simp only
    -- Use the direct lemma that works with Hypernat
    exact hyperPow2Seq_infinite_of_hypernat N hNinf
  exact infinitesimal_inv_of_infinite hsize

/-! ## Application: Wiener Measure from Hyperfinite Walks

The space of hyperfinite random walks, equipped with Loeb measure,
gives Wiener measure on continuous path space.
-/

/-- The hyperfinite path space: sequences of N coin flips -/
structure HyperfinitePathSpace where
  /-- The number of steps as a hypernatural -/
  numSteps : Foundation.Hypernat
  /-- The number of steps is infinite -/
  numSteps_infinite : Foundation.Hypernat.Infinite numSteps

namespace HyperfinitePathSpace

/-- The underlying probability space of a hyperfinite path space -/
noncomputable def probSpace (Ω : HyperfinitePathSpace) : InternalProbSpace :=
  walkProbSpace Ω.numSteps

/-- The time step dt = T/N for unit time interval T = 1 -/
noncomputable def dt (Ω : HyperfinitePathSpace) : ℝ* := 1 / Ω.numSteps.val

/-- The space step dx = √dt.
    Note: A proper definition requires hyperreal square root.
    We store dx as a hyperreal satisfying dx² = dt. -/
structure SqrtData (Ω : HyperfinitePathSpace) where
  /-- The value of √dt -/
  dx : ℝ*
  /-- The defining property: dx² = dt -/
  dx_sq : dx ^ 2 = Ω.dt
  /-- dx is positive -/
  dx_pos : 0 < dx

/-- The time step is infinitesimal -/
theorem dt_infinitesimal (Ω : HyperfinitePathSpace) : Infinitesimal Ω.dt := by
  unfold dt
  rw [one_div]
  have hinfN := Ω.numSteps_infinite
  rw [Foundation.Hypernat.infinite_iff_infinitePos] at hinfN
  have hinf : Infinite Ω.numSteps.val := Or.inl hinfN
  exact infinitesimal_inv_of_infinite hinf

/-- Individual paths have infinitesimal probability -/
theorem path_prob_infinitesimal (Ω : HyperfinitePathSpace) :
    Infinitesimal (Ω.probSpace.prob 1) :=
  singlePath_infinitesimal Ω.numSteps Ω.numSteps_infinite

/-- The pre-Loeb measure of individual paths is 0 -/
theorem path_preLoeb_zero (Ω : HyperfinitePathSpace) :
    preLoebMeasure Ω.probSpace 1 = 0 := by
  have hinf : Infinitesimal (Ω.probSpace.prob 1) := Ω.path_prob_infinitesimal
  have hfin : ¬Infinite (Ω.probSpace.prob 1) := hinf.not_infinite
  rw [preLoebMeasure_eq_st _ _ hfin]
  exact hinf.st_eq

end HyperfinitePathSpace

/-! ## Future Work: Cylinder Sets and Wiener Measure

A complete treatment would include:

1. **Cylinder sets**: Sets defined by constraints at finitely many times.
   For these, we can compute probabilities explicitly using the internal
   counting measure.

2. **Standard part map**: The map from hyperfinite paths to continuous paths
   via `HyperfiniteWalk.stdPartProcess`. This requires proving that walk
   values are finite almost surely, which needs Loeb measure.

3. **Anderson's theorem**: The pushforward of Loeb measure under the standard
   part map equals Wiener measure on C([0,T], ℝ). This is the crowning
   achievement of nonstandard probability theory.

With saturation now available in `Foundation.Saturation`, the key obstacle
is building the Carathéodory extension and proving path regularity properties.
-/

end SPDE.Nonstandard

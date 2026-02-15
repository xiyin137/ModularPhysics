/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.LocalCLT
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Foundation.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.ContinuousOn

/-!
# Cylinder Convergence Helpers

Infrastructure for proving `cylinder_prob_convergence`, the key bridge between
the hyperfinite random walk and Wiener measure.

## Main Results

* `gaussianDensitySigma_continuous` - continuity of the Gaussian density
* `scaledProb_eq_walkIntervalProb` - combinatorial rewrite of the scaled probability
* `binomProb_ratio_near_one` - ratio convergence for the local CLT

## Strategy

The proof of `cylinder_prob_convergence` proceeds by:
1. Rewriting scaledProb as a sum of binomial probabilities (combinatorial step)
2. Showing each binomial probability is close to the Gaussian density × mesh width
3. Showing the Riemann sum converges to the integral
-/

open Real Finset MeasureTheory

namespace SPDE.Nonstandard

/-! ## Continuity of Gaussian Density -/

/-- The Gaussian density gaussianDensitySigma(σ, ·) is continuous for σ > 0. -/
theorem gaussianDensitySigma_continuous {σ : ℝ} (hσ : 0 < σ) :
    Continuous (gaussianDensitySigma σ) := by
  unfold gaussianDensitySigma
  simp only [hσ, ↓reduceIte]
  apply Continuous.mul
  · exact continuous_const
  · exact continuous_exp.comp ((continuous_neg.comp (continuous_pow 2)).div_const _)

/-- The Gaussian density is nonneg -/
theorem gaussianDensitySigma_nonneg {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    0 ≤ gaussianDensitySigma σ x := by
  unfold gaussianDensitySigma
  simp only [hσ, ↓reduceIte]
  apply mul_nonneg
  · apply div_nonneg zero_le_one
    apply mul_nonneg (le_of_lt hσ)
    exact Real.sqrt_nonneg _
  · exact le_of_lt (Real.exp_pos _)

/-- The Gaussian density is bounded above by its peak value at x=0. -/
theorem gaussianDensitySigma_le_peak {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    gaussianDensitySigma σ x ≤ 1 / (σ * Real.sqrt (2 * Real.pi)) := by
  unfold gaussianDensitySigma
  simp only [hσ, ↓reduceIte]
  have hσ_sqrt : 0 < σ * Real.sqrt (2 * Real.pi) := by positivity
  apply mul_le_of_le_one_right (div_nonneg one_pos.le (le_of_lt hσ_sqrt))
  rw [Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (sq_nonneg x)
  · positivity

/-! ## Floor/Ceiling Ratio Convergence

For k = ⌊tN⌋, the ratio k/(tN) → 1 as N → ∞.
-/

/-- For t > 0, the floor ⌊tN⌋/N → t as N → ∞. -/
theorem floor_ratio_tendsto (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => (Nat.floor (t * N) : ℝ) / N) Filter.atTop (nhds t) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- For N ≥ N₀, 1/N < ε, so |⌊tN⌋/N - t| ≤ 1/N < ε
  use Nat.ceil (2 / ε)
  intro N hN
  rw [Real.dist_eq]
  -- N ≥ ⌈2/ε⌉ ≥ 2/ε > 1/ε > 0
  have hNε : (2 / ε : ℝ) ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hN_pos : (0 : ℝ) < N := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have h_floor_le : (Nat.floor (t * N) : ℝ) ≤ t * N := Nat.floor_le (by positivity)
  have h_floor_ge : t * N - 1 ≤ (Nat.floor (t * N) : ℝ) := by
    have := Nat.lt_floor_add_one (t * N)
    push_cast at this ⊢
    linarith [Nat.floor_le (show 0 ≤ t * N by positivity)]
  -- |⌊tN⌋/N - t| ≤ 1/N < ε
  -- Upper: ⌊tN⌋/N ≤ t (floor ≤ original)
  have hup : ↑⌊t * ↑N⌋₊ / ↑N ≤ t := by
    rw [div_le_iff₀ hN_pos]; linarith
  -- Lower: t - 1/N ≤ ⌊tN⌋/N (floor > original - 1)
  have hlow : t - 1 / ↑N ≤ ↑⌊t * ↑N⌋₊ / ↑N := by
    rw [le_div_iff₀ hN_pos]
    have : (t - 1 / ↑N) * ↑N = t * ↑N - 1 := by field_simp
    linarith
  -- 1/N < ε since N ≥ 2/ε, so εN ≥ 2 > 1
  have h1N_lt_ε : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hN_pos]
    have : ε * ↑N ≥ ε * (2 / ε) := by nlinarith
    have : ε * (2 / ε) = 2 := by field_simp
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- For t > 0 and N large enough, k = ⌊tN⌋ ≥ some threshold. -/
theorem floor_eventually_large (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, M ≤ Nat.floor (t * N) := by
  use Nat.ceil ((M + 1) / t)
  intro N hN
  have htN : (M : ℝ) < t * N := by
    calc (M : ℝ) < M + 1 := by linarith
      _ = t * ((M + 1) / t) := by field_simp
      _ ≤ t * Nat.ceil ((M + 1) / t) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
          exact Nat.le_ceil _
      _ ≤ t * N := by nlinarith [show (Nat.ceil ((↑M + 1) / t) : ℝ) ≤ N from by exact_mod_cast hN]
  exact Nat.le_floor (le_of_lt htN)

/-! ## Combinatorial Decomposition

Show that scaledProb (counting over Fin N → Bool) equals
a sum of binomial coefficients (walkIntervalProb).

The key fact: partialSumFin N flips k depends only on the first k flips,
so the remaining N-k flips contribute a factor of 2^(N-k).
-/

/-- partialSumFin only depends on flips with index < k.
    If two flip sequences agree on indices < k, they have the same partial sum. -/
theorem partialSumFin_depends_on_prefix (N : ℕ) (f g : Fin N → Bool) (k : ℕ)
    (hagree : ∀ i : Fin N, i.val < k → f i = g i) :
    partialSumFin N f k = partialSumFin N g k := by
  unfold partialSumFin
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  congr 1
  exact hagree i hi

/-- Count of true values among the first k positions of a flip sequence. -/
def countTruesBelow (N : ℕ) (f : Fin N → Bool) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < k ∧ f i = true)).card

/-- The set of indices < k in Fin N has cardinality k when k ≤ N. -/
theorem card_filter_lt (N k : ℕ) (hk : k ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k)).card = k := by
  have hbij : ((Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k)).card =
      (Finset.univ : Finset (Fin k)).card :=
    Finset.card_bij'
      (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2⟩)
      (fun b _ => Fin.castLE hk b)
      (fun _ _ => Finset.mem_univ _)
      (fun b _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩)
      (fun _ _ => Fin.ext rfl)
      (fun _ _ => Fin.ext rfl)
  rw [hbij, Finset.card_univ, Fintype.card_fin]

/-- partialSumFin equals 2 * countTruesBelow - k (as integers).
    Since each true contributes +1 and each false contributes -1,
    the sum is #true - #false = #true - (k - #true) = 2·#true - k. -/
theorem partialSumFin_eq_countTrues (N : ℕ) (f : Fin N → Bool) (k : ℕ) (hk : k ≤ N) :
    (partialSumFin N f k : ℤ) = 2 * ↑(countTruesBelow N f k) - ↑k := by
  unfold partialSumFin countTruesBelow
  set s := (Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k) with hs_def
  have hcard_s : s.card = k := card_filter_lt N k hk
  -- Decompose s into true and false parts
  have hcover : (s.filter (fun i => f i = true) ∪
      s.filter (fun a => ¬(f a = true))) = s :=
    Finset.filter_union_filter_not_eq (p := fun i => f i = true) s
  have hdisj : Disjoint (s.filter (fun i => f i = true))
      (s.filter (fun a => ¬(f a = true))) :=
    Finset.disjoint_filter_filter_not s s (fun i => f i = true)
  -- Rewrite sum using the partition
  conv_lhs => rw [← hcover]
  rw [Finset.sum_union hdisj]
  -- On true part, boolToInt = 1
  have htrue_val : ∀ i ∈ s.filter (fun i => f i = true), boolToInt (f i) = (1 : ℤ) := by
    intro i hi; rw [Finset.mem_filter] at hi
    unfold boolToInt; simp [hi.2]
  -- On false part, boolToInt = -1
  have hfalse_val : ∀ i ∈ s.filter (fun a => ¬(f a = true)),
      boolToInt (f i) = (-1 : ℤ) := by
    intro i hi; rw [Finset.mem_filter] at hi
    unfold boolToInt; simp [hi.2]
  rw [Finset.sum_congr rfl htrue_val, Finset.sum_congr rfl hfalse_val]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg_one]
  -- Card computation
  have hcard_union : (s.filter (fun i => f i = true)).card +
      (s.filter (fun a => ¬(f a = true))).card = k := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hcover] at h; rw [← h, hcard_s]
  -- True card equals countTruesBelow
  suffices htrue : (s.filter (fun i => f i = true)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < k ∧ f i = true)).card by
    rw [htrue] at hcard_union ⊢; omega
  congr 1; ext i
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, ⟨(Finset.mem_filter.mp hi.1).2, hi.2⟩⟩
  · intro hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1⟩, hi.2.2⟩

/-- Number of boolean functions on Fin k with exactly j trues equals C(k,j).
    Uses bijection with Finset.powersetCard j univ. -/
theorem card_bool_trues_eq_choose (k j : ℕ) (hj : j ≤ k) :
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => (Finset.univ.filter (fun i => g i = true)).card = j)).card = Nat.choose k j := by
  -- Rewrite RHS as card of powersetCard
  rw [show Nat.choose k j = ((Finset.univ : Finset (Fin k)).powersetCard j).card from by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]]
  -- Bijection with powersetCard j univ via g ↦ {i | g i = true}
  exact Finset.card_bij'
    (fun g _ => Finset.univ.filter (fun i => g i = true))
    (fun S _ => fun i => decide (i ∈ S))
    (fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hg⟩)
    (fun S hS => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.mem_powersetCard] at hS
      have : Finset.univ.filter (fun i => decide (i ∈ S) = true) = S := by
        ext i; simp [Finset.mem_filter, decide_eq_true_eq]
      rw [show (Finset.univ.filter (fun i => (fun i => decide (i ∈ S)) i = true)).card =
          S.card from by rw [this]]; exact hS.2)
    (fun g _ => by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    decide_eq_true_eq]; cases g i <;> simp)
    (fun S _ => by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    decide_eq_true_eq])

/-- countTruesBelow equals the cardinality of a filter over the prefix type Fin k. -/
private lemma countTruesBelow_eq_filter_prefix {N k : ℕ} (f : Fin N → Bool) (hk : k ≤ N) :
    countTruesBelow N f k =
    ((Finset.univ : Finset (Fin k)).filter
      (fun i => f ⟨i.val, i.isLt.trans_le hk⟩ = true)).card := by
  unfold countTruesBelow
  exact Finset.card_bij'
    (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2.1⟩)
    (fun b _ => ⟨b.val, b.isLt.trans_le hk⟩)
    (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩)
    (fun b hb => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨b.isLt, (Finset.mem_filter.mp hb).2⟩⟩)
    (fun _ _ => Fin.ext rfl)
    (fun _ _ => Fin.ext rfl)

/-- Product counting: #{f : Fin N → Bool | countTruesBelow f k = j} = C(k,j) × 2^(N-k).
    Each choice of prefix (j trues among k) combines with any suffix. -/
theorem card_prefix_suffix_product (N k j : ℕ) (hk : k ≤ N) (hj : j ≤ k) :
    ((Finset.univ : Finset (Fin N → Bool)).filter
      (fun f => countTruesBelow N f k = j)).card = Nat.choose k j * 2 ^ (N - k) := by
  -- Define the target set
  let prefixSet := (Finset.univ : Finset (Fin k → Bool)).filter
    (fun g => (Finset.univ.filter (fun i => g i = true)).card = j)
  let suffixSet := (Finset.univ : Finset (Fin (N - k) → Bool))
  let target := prefixSet ×ˢ suffixSet
  -- Define forward and backward maps
  let fwd : (Fin N → Bool) → (Fin k → Bool) × (Fin (N - k) → Bool) :=
    fun f => (fun i => f ⟨i.val, i.isLt.trans_le hk⟩, fun i => f ⟨k + i.val, by omega⟩)
  let bwd : (Fin k → Bool) × (Fin (N - k) → Bool) → (Fin N → Bool) :=
    fun p => fun i => if hlt : i.val < k then p.1 ⟨i.val, hlt⟩
                      else p.2 ⟨i.val - k, by omega⟩
  -- Step 1: card(source) = card(target) via bijection
  let source := (Finset.univ : Finset (Fin N → Bool)).filter
    (fun f => countTruesBelow N f k = j)
  suffices hsuff : source.card = target.card by
    rw [hsuff, Finset.card_product, card_bool_trues_eq_choose k j hj]
    congr 1
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- Step 2: Establish bijection using card_bij'
  show source.card = target.card
  apply Finset.card_bij'
    (fun f _ => fwd f) (fun p _ => bwd p)
  · -- hi: forward maps source into target
    intro f hf
    simp only [source, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [target, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
               suffixSet]
    refine ⟨?_, trivial⟩
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← countTruesBelow_eq_filter_prefix f hk]; exact hf
  · -- hj_mem: backward maps target into source
    intro p hp
    simp only [target, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
               suffixSet] at hp
    simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [countTruesBelow_eq_filter_prefix (bwd p) hk]
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [← hp.1]; congr 1
    refine Finset.filter_congr (fun i _ => ?_)
    dsimp only [bwd]; rw [dif_pos i.isLt]
  · -- left_inv: bwd (fwd f) = f
    intro f _; ext ⟨i, hi⟩
    show bwd (fwd f) ⟨i, hi⟩ = f ⟨i, hi⟩
    dsimp only [fwd, bwd]
    split
    · next hlt => rfl
    · next hlt =>
        simp only [show k + (i - k) = i from by omega]
  · -- right_inv: fwd (bwd p) = p
    intro p _
    show fwd (bwd p) = p
    ext ⟨i, hi⟩
    · -- First component
      show (fwd (bwd p)).1 ⟨i, hi⟩ = p.1 ⟨i, hi⟩
      simp only [fwd, bwd, show (i : ℕ) < k from hi, ↓reduceDIte]
    · -- Second component
      show (fwd (bwd p)).2 ⟨i, hi⟩ = p.2 ⟨i, hi⟩
      dsimp only [fwd, bwd]
      simp only [show ¬((k + ↑i : ℕ) < k) from by omega, ↓reduceDIte,
                 show k + (i : ℕ) - k = i from by omega]

/-- The count of flip sequences satisfying a condition on S_k equals
    walkIntervalProb(k, a, b, 1/√N) × 2^N.

    Specifically:
    #{f : Fin N → Bool | a ≤ S_k(f)/√N ≤ b} / 2^N = walkIntervalProb(k, a, b, 1/√N)

    where S_k(f) = partialSumFin N f k depends only on the first k flips. -/
theorem scaledProb_eq_walkIntervalProb (N : ℕ) (k : ℕ) (hk : k ≤ N) (a b : ℝ)
    (hN : 0 < N) :
    ((Finset.univ : Finset (Fin N → Bool)).filter
      (fun flips =>
        let walk := (partialSumFin N flips k : ℝ) / Real.sqrt N
        a ≤ walk ∧ walk ≤ b)).card / (2^N : ℝ) =
    walkIntervalProb k a b (1 / Real.sqrt N) := by
  sorry

/-! ## Ratio Convergence

The key analytical step: each binomial probability is close to
the Gaussian density × mesh width.

C(k, j) / 2^k ≈ gaussianDensitySigma(√t, (2j-k)/√N) × (2/√N)
-/

/-- For any δ > 0 and t > 0, for N large enough and k = ⌊tN⌋:
    The ratio C(k,j)/2^k / [gaussianDensitySigma(√t, x_j) × Δx] is in (1-δ, 1+δ)
    for all lattice points x_j = (2j-k)/√N in [a, b].

    This is the quantitative form of the local CLT ratio convergence. -/
theorem binomProb_ratio_near_one (a b : ℝ) (t : ℝ) (ha : a < b) (ht : 0 < t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      ∀ j : ℕ, j ≤ k →
        let x := (2 * (j : ℝ) - k) / Real.sqrt N
        a ≤ x → x ≤ b →
        let binomP := (Nat.choose k j : ℝ) / 2^k
        let gaussP := gaussianDensitySigma (Real.sqrt t) x * (2 / Real.sqrt N)
        0 < gaussP → |binomP / gaussP - 1| < δ := by
  -- The ratio decomposes as:
  -- binomP / gaussP = θ × (1/√(1-v²)) × exp(-k(h(v)-v²)/2) × √(k/(tN)) × exp(correction)
  -- where v = (2j-k)/k and θ = stirling triple ratio.
  -- Each factor → 1 uniformly for x_j ∈ [a, b]:
  -- 1. θ → 1 by stirlingSeq_triple_ratio_near_one
  -- 2. 1/√(1-v²) → 1 since v = (2j-k)/k ≈ x√N/k ≈ x/(√t√N) → 0
  -- 3. exp correction → 1 since k(h(v)-v²) = O(s⁴/k³) → 0
  -- 4. √(k/(tN)) → 1 since k/(tN) → 1
  -- 5. exp(s²(1/(2k) - 1/(2tN))) → 1 since |1/k - 1/(tN)| → 0
  sorry

/-! ## Riemann Sum Convergence

The sum of Gaussian density values × mesh converges to the integral.
-/

/-- A Riemann sum with lattice spacing 2/√N over [a, b] converges to the integral.
    This uses the continuity of gaussianDensitySigma and standard Riemann sum theory. -/
theorem gaussDensity_Riemann_sum_converges (a b : ℝ) (t : ℝ) (ha : a ≤ b) (ht : 0 < t) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      |∑ j ∈ Finset.range (k + 1),
        (if a ≤ (2 * (j : ℝ) - k) / Real.sqrt N ∧ (2 * (j : ℝ) - k) / Real.sqrt N ≤ b
         then gaussianDensitySigma (Real.sqrt t) ((2 * (j : ℝ) - k) / Real.sqrt N) * (2 / Real.sqrt N)
         else 0) -
       ∫ x in Set.Icc a b, gaussianDensitySigma (Real.sqrt t) x| < δ := by
  -- The sum is a Riemann sum of a continuous function with mesh 2/√N → 0.
  -- By the standard Riemann sum convergence theorem, it converges to the integral.
  sorry

/-! ## Tail Bounds for Binomial Sums

The sum of binomial probabilities outside [-C√k, C√k] is small.

### Proof Strategy

We use the Chernoff method directly on the binomial sum:
1. Exponential Markov: Σ_{j : 2j-k > t} C(k,j)/2^k ≤ exp(-λt) × MGF(λ)
2. MGF computation: Σ C(k,j)/2^k × exp(λ(2j-k)) = cosh(λ)^k
3. Chernoff bound: cosh(λ) ≤ exp(λ²/2)
4. Optimize λ = C/√k with t = C√k → exp(-C²/2)
-/

/-- Exponential Markov inequality for non-negative weighted sums.
    For any λ > 0 and threshold t:
    Σ_{j : f(j) > t} w_j ≤ exp(-λt) × Σ_j w_j × exp(λ f(j)). -/
theorem weighted_exp_markov {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (l t : ℝ) (hl : 0 < l) :
    ∑ i ∈ s.filter (fun i => t < f i), w i ≤
    Real.exp (-l * t) * ∑ i ∈ s, w i * Real.exp (l * f i) := by
  calc ∑ i ∈ s.filter (fun i => t < f i), w i
      = ∑ i ∈ s.filter (fun i => t < f i), w i * 1 := by simp
    _ ≤ ∑ i ∈ s.filter (fun i => t < f i),
        w i * Real.exp (l * (f i - t)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hfi : t < f i := by
          simp only [Finset.mem_filter] at hi; exact hi.2
        apply mul_le_mul_of_nonneg_left _ (hw i (Finset.mem_of_mem_filter i hi))
        linarith [Real.add_one_le_exp (l * (f i - t)),
                  mul_nonneg (le_of_lt hl) (le_of_lt (sub_pos.mpr hfi))]
    _ = ∑ i ∈ s.filter (fun i => t < f i),
        w i * (Real.exp (-l * t) * Real.exp (l * f i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.exp_add]
        congr 1; ring_nf
    _ = ∑ i ∈ s.filter (fun i => t < f i),
        Real.exp (-l * t) * (w i * Real.exp (l * f i)) := by
        apply Finset.sum_congr rfl
        intro i _; ring
    _ = Real.exp (-l * t) * ∑ i ∈ s.filter (fun i => t < f i),
        w i * Real.exp (l * f i) := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (-l * t) * ∑ i ∈ s, w i * Real.exp (l * f i) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg (hw i (by assumption)) (le_of_lt (Real.exp_pos _))

/-- The binomial MGF: Σ_{j=0}^k C(k,j)/2^k × exp(λ(2j-k)) = cosh(λ)^k.
    Proof uses the binomial theorem: (x+y)^k = Σ C(k,j) x^j y^{k-j}
    with x = exp(λ)/2, y = exp(-λ)/2. -/
theorem binomial_mgf (k : ℕ) (l : ℝ) :
    ∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) / 2^k * Real.exp (l * (2 * (j : ℝ) - ↑k)) =
    (Real.cosh l) ^ k := by
  -- cosh(l) = (exp l + exp(-l))/2 = exp(l)/2 + exp(-l)/2
  have hcosh : Real.cosh l = Real.exp l / 2 + Real.exp (-l) / 2 := by
    rw [Real.cosh_eq]; ring
  rw [hcosh, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- Goal: (exp l / 2)^j * (exp(-l) / 2)^{k-j} * C(k,j) = C(k,j)/2^k * exp(l*(2j-k))
  -- Step 1: Split (a/b)^n into a^n/b^n
  rw [div_pow, div_pow]
  -- Step 2: Convert (exp x)^n to exp(n*x) using exp_nat_mul
  rw [← Real.exp_nat_mul l, ← Real.exp_nat_mul (-l)]
  -- Step 3: Combine the two fractions
  rw [div_mul_div_comm]
  -- Step 4: Combine exponents
  rw [← Real.exp_add]
  -- Step 5: Simplify 2^j * 2^{k-j} = 2^k
  rw [show (2 : ℝ) ^ j * 2 ^ (k - j) = 2 ^ k from by rw [← pow_add]; congr 1; omega]
  -- Step 6: Simplify exponent: j*l + (k-j)*(-l) = l*(2j-k)
  rw [show ↑j * l + ↑(k - j) * (-l) = l * (2 * ↑j - ↑k) from by
    push_cast [Nat.cast_sub hj_le]; ring]
  -- Step 7: Commutativity
  ring

/-- One-sided Chernoff bound for positive tail of binomial:
    Σ_{j : 2j-k > t} C(k,j)/2^k ≤ exp(-t²/(2k)) for t > 0. -/
theorem binomial_chernoff_upper (k : ℕ) (t : ℝ) (hk : 0 < k) (ht : 0 < t) :
    ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => t < 2 * (j : ℝ) - ↑k),
      (Nat.choose k j : ℝ) / 2^k ≤ Real.exp (-t^2 / (2 * k)) := by
  -- Use exponential Markov with λ = t/k and f(j) = 2j - k
  set l := t / (k : ℝ) with hl_def
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hl_pos : 0 < l := div_pos ht hk_pos
  -- Apply weighted exponential Markov
  have hmarkov := weighted_exp_markov (Finset.range (k + 1))
    (fun j => (Nat.choose k j : ℝ) / 2^k)
    (fun j => 2 * (j : ℝ) - ↑k)
    (fun j _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k))
    l t hl_pos
  -- The MGF equals cosh(l)^k
  have hmgf : ∑ j ∈ Finset.range (k + 1),
      (Nat.choose k j : ℝ) / 2^k * Real.exp (l * (2 * ↑j - ↑k)) =
      (Real.cosh l) ^ k := binomial_mgf k l
  -- cosh(l)^k ≤ exp(kl²/2) = exp(t²/(2k))
  have hcosh : (Real.cosh l) ^ k ≤ Real.exp (↑k * l ^ 2 / 2) := by
    calc (Real.cosh l) ^ k ≤ (Real.exp (l ^ 2 / 2)) ^ k :=
          pow_le_pow_left₀ (by positivity) (Real.cosh_le_exp_half_sq l) k
      _ = Real.exp (↑k * l ^ 2 / 2) := by
          rw [← Real.exp_nat_mul (l ^ 2 / 2) k]; congr 1; ring
  -- Combine: bound ≤ exp(-lt) × exp(kl²/2) = exp(kl²/2 - lt) = exp(-t²/(2k))
  calc ∑ j ∈ (Finset.range (k + 1)).filter _, (Nat.choose k j : ℝ) / 2^k
      ≤ Real.exp (-l * t) * ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) / 2^k * Real.exp (l * (2 * ↑j - ↑k)) := hmarkov
    _ = Real.exp (-l * t) * (Real.cosh l) ^ k := by rw [hmgf]
    _ ≤ Real.exp (-l * t) * Real.exp (↑k * l ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left hcosh (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-l * t + ↑k * l ^ 2 / 2) := by rw [← Real.exp_add]
    _ = Real.exp (-t ^ 2 / (2 * ↑k)) := by
        congr 1
        rw [hl_def]
        field_simp
        ring

/-- One-sided Chernoff bound for negative tail (by symmetry). -/
theorem binomial_chernoff_lower (k : ℕ) (t : ℝ) (hk : 0 < k) (ht : 0 < t) :
    ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t),
      (Nat.choose k j : ℝ) / 2^k ≤ Real.exp (-t^2 / (2 * k)) := by
  -- By symmetry j ↦ k - j, the negative tail sum equals the positive tail sum
  have hupper := binomial_chernoff_upper k t hk ht
  -- Show the two sums are equal via the bijection j ↦ k - j
  suffices heq : ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t),
      (Nat.choose k j : ℝ) / 2^k =
    ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => t < 2 * (j : ℝ) - ↑k),
      (Nat.choose k j : ℝ) / 2^k by
    rw [heq]; exact hupper
  -- Use sum_nbij' with inverse j ↦ k - j
  apply Finset.sum_nbij' (fun j => k - j) (fun j => k - j)
  · -- hi: maps negative filter to positive filter
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨by omega, ?_⟩
    push_cast [Nat.cast_sub (by omega : j ≤ k)]
    linarith [hj.2]
  · -- hj: maps positive filter to negative filter
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨by omega, ?_⟩
    push_cast [Nat.cast_sub (by omega : j ≤ k)]
    linarith [hj.2]
  · -- left_inv: k - (k - j) = j
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    omega
  · -- right_inv: k - (k - j) = j
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    omega
  · -- Values match: C(k, k-j)/2^k = C(k, j)/2^k
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    congr 1; exact_mod_cast (Nat.choose_symm (by omega : j ≤ k)).symm

/-- Tail bound: For the random walk of length k, the probability of being
    outside [-t, t] is at most 2exp(-t²/(2k)) (from Hoeffding). -/
theorem binomial_tail_small (k : ℕ) (C : ℝ) (hk : 0 < k) (hC : 0 < C) :
    ∑ j ∈ (Finset.range (k + 1)).filter
      (fun j : ℕ => C * Real.sqrt k < |(2 * (j : ℝ) - k)|),
      (Nat.choose k j : ℝ) / 2^k ≤ 2 * Real.exp (-C^2 / 2) := by
  -- Split |2j-k| > C√k into two tails: 2j-k > C√k and 2j-k < -C√k
  set t := C * Real.sqrt k with ht_def
  have ht : 0 < t := mul_pos hC (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk))
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- The |·| filter is subset of the union of one-sided filters
  have hwnonneg : ∀ j ∈ Finset.range (k + 1),
      0 ≤ (Nat.choose k j : ℝ) / 2^k :=
    fun _ _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
  -- The two one-sided filters are disjoint (can't have both 2j-k > t and 2j-k < -t)
  have hdisjoint : Disjoint
      ((Finset.range (k + 1)).filter (fun j : ℕ => t < 2 * (j : ℝ) - ↑k))
      ((Finset.range (k + 1)).filter (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t)) := by
    simp only [Finset.disjoint_filter]
    intro j _ h1 h2; linarith
  calc ∑ j ∈ (Finset.range (k + 1)).filter
          (fun j : ℕ => t < |(2 * (j : ℝ) - ↑k)|),
        (Nat.choose k j : ℝ) / 2^k
      ≤ ∑ j ∈ ((Finset.range (k + 1)).filter (fun j : ℕ => t < 2 * (j : ℝ) - ↑k)) ∪
           ((Finset.range (k + 1)).filter (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t)),
        (Nat.choose k j : ℝ) / 2^k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hj ⊢
          have habs := hj.2
          rw [lt_abs] at habs
          rcases habs with h | h
          · exact Or.inl ⟨hj.1, h⟩
          · exact Or.inr ⟨hj.1, by linarith⟩
        · intro j hj _
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hj
          exact hwnonneg j (Finset.mem_range.mpr (by rcases hj with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h))
    _ = (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => t < 2 * (j : ℝ) - ↑k),
          (Nat.choose k j : ℝ) / 2^k) +
        (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t),
          (Nat.choose k j : ℝ) / 2^k) :=
        Finset.sum_union hdisjoint
    _ ≤ Real.exp (-t^2 / (2 * k)) + Real.exp (-t^2 / (2 * k)) :=
        add_le_add (binomial_chernoff_upper k t hk ht) (binomial_chernoff_lower k t hk ht)
    _ = 2 * Real.exp (-t^2 / (2 * k)) := by ring
    _ = 2 * Real.exp (-C^2 / 2) := by
        congr 1; congr 1
        rw [ht_def, mul_pow, Real.sq_sqrt (le_of_lt hk_pos)]
        field_simp

end SPDE.Nonstandard

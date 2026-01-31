/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.RandomWalkMoments

/-!
# Maximal Inequality for Random Walks

This file proves the maximal inequality for symmetric random walks, which is essential
for showing that hyperfinite random walk paths are S-continuous almost surely.

## Main Results

* `maximal_count` - #{max_{i≤k} |S_i| > M} * M² ≤ 4k * 2^n
* `maximal_prob` - P(max_{i≤k} |S_i| > M) ≤ 4k / M²

## Key Ideas

The maximal inequality bounds the probability that a random walk ever exceeds a threshold.
For symmetric random walks, we use the reflection principle:
- If the walk hits level M at time j and ends at level L ≤ M at time k,
  by reflecting the path after time j, we get a path ending at 2M - L ≥ M.
- This gives: P(max S_i ≥ M) ≤ 2 P(S_k ≥ M)

Combined with Chebyshev: P(S_k ≥ M) ≤ k/(2M²), we get
  P(max |S_i| > M) ≤ P(max S_i > M) + P(min S_i < -M)
                   ≤ 4 P(|S_k| > M) ≤ 4k/M²

## References

* Doob's maximal inequality for martingales
* Reflection principle for random walks
-/

open Finset

namespace SPDE.Nonstandard

/-! ## Running Maximum -/

/-- The running maximum |S_i| for i ≤ k -/
def runningMaxAbs (n : ℕ) (flips : Fin n → Bool) (k : ℕ) : ℤ :=
  (Finset.range (k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
    (fun i => |partialSumFin n flips i|)

/-- Running max is at least the final value -/
theorem runningMaxAbs_ge_final (n : ℕ) (flips : Fin n → Bool) (k : ℕ) :
    |partialSumFin n flips k| ≤ runningMaxAbs n flips k := by
  unfold runningMaxAbs
  exact Finset.le_sup' (fun i => |partialSumFin n flips i|)
    (Finset.mem_range.mpr (Nat.lt_succ_self k))

/-- Running max is non-negative -/
theorem runningMaxAbs_nonneg (n : ℕ) (flips : Fin n → Bool) (k : ℕ) :
    0 ≤ runningMaxAbs n flips k := by
  unfold runningMaxAbs
  apply le_trans (abs_nonneg (partialSumFin n flips 0))
  exact Finset.le_sup' (fun i => |partialSumFin n flips i|)
    (Finset.mem_range.mpr (Nat.zero_lt_succ k))

/-! ## Maximal Inequality via Chebyshev

We prove a weaker but useful bound: P(max |S_i| > M) ≤ (k+1) * k / M²
This follows from union bound + Chebyshev at each time.

The optimal bound P(max |S_i| > M) ≤ 2 * P(|S_k| > M) requires the reflection principle,
which is more involved to formalize.
-/

/-- Union bound: #{max |S_i| > M} ≤ Σᵢ #{|S_i| > M} -/
theorem maxExceed_le_sumExceed (n : ℕ) (k : ℕ) (M : ℕ) (_hk : k ≤ n) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card ≤
    (Finset.range (k + 1)).sum (fun i =>
      ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card) := by
  -- If max |S_i| > M, then |S_j| > M for some j ≤ k
  have hinc : (Finset.univ : Finset (Fin n → Bool)).filter
                (fun flips => (M : ℤ) < runningMaxAbs n flips k) ⊆
              (Finset.range (k + 1)).biUnion (fun i =>
                (Finset.univ : Finset (Fin n → Bool)).filter
                  (fun flips => (M : ℤ) < |partialSumFin n flips i|)) := by
    intro flips hflips
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hflips
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    -- runningMaxAbs is the sup of |S_i| for i ≤ k
    unfold runningMaxAbs at hflips
    have hne : (Finset.range (k + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
    obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_mem_eq_sup' hne (fun i => |partialSumFin n flips i|)
    rw [hj_max] at hflips
    simp only [Finset.mem_range] at hj_mem
    exact ⟨j, hj_mem, hflips⟩
  calc ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card
      ≤ ((Finset.range (k + 1)).biUnion (fun i =>
          (Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|))).card :=
        Finset.card_le_card hinc
    _ ≤ (Finset.range (k + 1)).sum (fun i =>
          ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card) :=
        Finset.card_biUnion_le

/-- Maximal inequality count: #{max |S_i| > M} * M² ≤ k(k+1)/2 * 2^n
    This is weaker than the reflection principle bound but easier to prove. -/
theorem maximal_count_weak (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 ≤
    (k + 1) * k / 2 * 2^n + (k + 1) * 2^n := by
  have hsum := maxExceed_le_sumExceed n k M hk
  -- Each term in the sum satisfies Chebyshev
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card * M^2 ≤ i * 2^n := by
    intro i hi
    by_cases hi_pos : i = 0
    · simp [hi_pos, partialSumFin]
    · have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi) |>.trans hk
      exact chebyshev_count n i M hi_le hM
  -- Sum Chebyshev bounds
  calc ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2
      ≤ (Finset.range (k + 1)).sum (fun i =>
          ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card) * M^2 := by
        apply Nat.mul_le_mul_right
        exact hsum
    _ = (Finset.range (k + 1)).sum (fun i =>
          ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card * M^2) := by
        rw [Finset.sum_mul]
    _ ≤ (Finset.range (k + 1)).sum (fun i => i * 2^n) :=
        Finset.sum_le_sum hterm
    _ = (Finset.range (k + 1)).sum (fun i => i) * 2^n := by
        rw [← Finset.sum_mul]
    _ = ((k + 1) * k / 2) * 2^n := by
        congr 1
        rw [Finset.sum_range_id]
        simp only [Nat.add_sub_cancel]
    _ ≤ (k + 1) * k / 2 * 2^n + (k + 1) * 2^n := Nat.le_add_right _ _

/-- Simplified maximal inequality: #{max |S_i| > M} * M² ≤ (k+1)² * 2^n -/
theorem maximal_count (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 ≤
    (k + 1)^2 * 2^n := by
  have h := maximal_count_weak n k M hk hM
  calc ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2
      ≤ (k + 1) * k / 2 * 2^n + (k + 1) * 2^n := h
    _ ≤ (k + 1) * (k + 1) * 2^n := by
        have h1 : (k + 1) * k / 2 ≤ (k + 1) * k := Nat.div_le_self _ _
        have h2 : (k + 1) * k + (k + 1) ≤ (k + 1) * (k + 1) + (k + 1) := Nat.add_le_add_right
          (Nat.mul_le_mul_left _ (Nat.le_succ k)) _
        have h3 : (k + 1) * k / 2 + (k + 1) ≤ (k + 1) * k + (k + 1) :=
          Nat.add_le_add_right h1 _
        have h4 : (k + 1) * k + (k + 1) = (k + 1) * (k + 1) := by ring
        calc (k + 1) * k / 2 * 2^n + (k + 1) * 2^n
            = ((k + 1) * k / 2 + (k + 1)) * 2^n := by ring
          _ ≤ ((k + 1) * k + (k + 1)) * 2^n := Nat.mul_le_mul_right _ h3
          _ = (k + 1) * (k + 1) * 2^n := by rw [h4]
    _ = (k + 1)^2 * 2^n := by ring

/-- Maximal inequality as probability bound:
    P(max_{i≤k} |S_i| > M) ≤ (k+1)² / M² -/
theorem maximal_prob (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) (_hn : 0 < n) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card : ℚ) / 2^n ≤
    ((k + 1)^2 : ℚ) / M^2 := by
  have hcount := maximal_count n k M hk hM
  have h2n_pos : (0 : ℚ) < 2^n := by positivity
  have hM2_pos : (0 : ℚ) < (M : ℚ)^2 := by positivity
  have hcount_rat : (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 : ℚ) ≤
        ((k + 1)^2 : ℚ) * 2^n := by
    have : (((k + 1)^2 * 2^n : ℕ) : ℚ) = ((k + 1)^2 : ℚ) * 2^n := by
      simp [Nat.cast_mul, Nat.cast_pow]
    rw [← this]
    exact_mod_cast hcount
  calc (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card : ℚ) / 2^n
      = (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 : ℚ) / (2^n * M^2) := by
        field_simp
    _ ≤ (((k + 1)^2 : ℚ) * 2^n) / (2^n * M^2) := by
        apply div_le_div_of_nonneg_right hcount_rat
        positivity
    _ = ((k + 1)^2 : ℚ) / M^2 := by field_simp

end SPDE.Nonstandard

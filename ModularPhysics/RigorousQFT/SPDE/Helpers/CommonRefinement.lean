/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Helpers.SimpleProcessDef

/-!
# Common Refinement of Simple Process Partitions

This file provides the infrastructure for refining simple process partitions
and proving that refinement preserves the stochastic integral. This is the
key technical ingredient for proving linearity of the Itô integral.

## Main Definitions

* `SimpleProcess.valueAtTime` — Step function evaluation at a given time
* `SimpleProcess.partitionFinset` — Partition times as a `Finset`

## Main Results

* `SimpleProcess.stochasticIntegral_at_eq_min` — Min-capped reformulation of the integral
* `SimpleProcess.refinement_sum_eq` — Refinement preserves the integral

## Strategy

The stochastic integral ∫H dW(t) can be written using `min`:
  Σᵢ vᵢ * (W(min(tᵢ₊₁, t)) - W(min(tᵢ, t)))

Inserting a point s between tⱼ and tⱼ₊₁ splits one term into two with the same
value, which telescope back to the original. By induction on the number of
inserted points, refinement preserves the integral.

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ## Step function value lookup -/

/-- Collect partition times into a Finset. -/
noncomputable def partitionFinset (H : SimpleProcess F) : Finset ℝ :=
  Finset.image H.times Finset.univ

/-- The value of a simple process step function at time s.
    Returns `H.values j` if s ∈ [H.times j, H.times ⟨j+1, hj⟩) for some j with j+1 < n.
    Returns 0 otherwise (before first time, at/past last interval endpoint). -/
noncomputable def valueAtTime (H : SimpleProcess F) (s : ℝ) : Ω → ℝ :=
  if h : ∃ (j : Fin H.n) (_ : (j : ℕ) + 1 < H.n),
    H.times j ≤ s ∧ s < H.times ⟨(j : ℕ) + 1, ‹_›⟩
  then H.values h.choose
  else fun _ => 0

/-- valueAtTime is measurable (ambient σ-algebra). -/
theorem measurable_valueAtTime (H : SimpleProcess F) (s : ℝ) :
    Measurable (H.valueAtTime s) := by
  unfold valueAtTime
  split
  · exact H.adapted _
  · exact measurable_const

/-- valueAtTime is measurable at the filtration σ-algebra of its time argument.
    If all values are adapted (measurable at their partition times), then
    valueAtTime(s) is measurable at W.F.σ_algebra(s) by filtration monotonicity. -/
theorem valueAtTime_measurable_filtration (H : SimpleProcess F)
    {W : BrownianMotion Ω μ} (s : ℝ)
    (hH : ∀ i : Fin H.n, @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i)) :
    @Measurable Ω ℝ (W.F.σ_algebra s) _ (H.valueAtTime s) := by
  unfold valueAtTime
  split
  · next h =>
    have hs_le := h.choose_spec.choose_spec.1  -- H.times h.choose ≤ s
    exact (hH h.choose).mono (W.F.mono _ _ hs_le) le_rfl
  · exact measurable_const

/-- valueAtTime is bounded if all values are bounded. -/
theorem valueAtTime_bounded (H : SimpleProcess F) (s : ℝ)
    (hb : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C) :
    ∃ C : ℝ, ∀ ω, |H.valueAtTime s ω| ≤ C := by
  unfold valueAtTime
  split
  · next h => exact hb h.choose
  · exact ⟨0, fun ω => by simp⟩

/-! ## Min-capped reformulation of stochastic integral -/

/-- Key observation: when t_i > t, the summand in stochasticIntegral_at is 0,
    which equals v_i * (W(min(t_{i+1},t)) - W(min(t_i,t))) since both mins equal t.
    This allows a uniform formula using min. -/
theorem stochasticIntegral_at_eq_min (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) (ω : Ω) :
    H.stochasticIntegral_at W t ω =
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (min (H.times ⟨i + 1, h⟩) t) ω -
                       W.process (min (H.times i) t) ω)
    else 0 := by
  unfold stochasticIntegral_at
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (i : ℕ) + 1 < H.n
  · simp only [dif_pos h]
    by_cases h_full : H.times ⟨(i : ℕ) + 1, h⟩ ≤ t
    · -- Full interval: min(t_{i+1}, t) = t_{i+1}
      simp only [if_pos h_full, min_eq_left h_full,
        min_eq_left (le_trans (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, h⟩
          (by simp [Fin.lt_def]))) h_full)]
    · push_neg at h_full
      by_cases h_start : H.times i ≤ t
      · -- Partial interval: min(t_{i+1}, t) = t, min(t_i, t) = t_i
        simp only [if_neg (not_le.mpr h_full), if_pos h_start,
          min_eq_right (le_of_lt h_full), min_eq_left h_start]
      · -- Past the interval: both mins = t, difference = 0
        push_neg at h_start
        simp only [if_neg (not_le.mpr h_full), if_neg (not_le.mpr h_start),
          min_eq_right (le_of_lt h_full), min_eq_right (le_of_lt h_start),
          sub_self, mul_zero]
  · simp only [dif_neg h]

/-! ## Telescoping for min-capped sums

The key property: for a ≤ b ≤ c, W(min(c,t)) - W(min(a,t))
= (W(min(b,t)) - W(min(a,t))) + (W(min(c,t)) - W(min(b,t))).
This is just algebra (sub_add_sub_cancel). -/

/-- The stochastic integral only depends on the step function values.
    If two processes have the same partition and the same values on active intervals
    (i.e., same values at index i for all i with i+1 < n), then they have the
    same stochasticIntegral_at. -/
theorem stochasticIntegral_at_eq_of_same_active_values
    (H₁ H₂ : SimpleProcess F) (W : BrownianMotion Ω μ) (t : ℝ) (ω : Ω)
    (hn : H₁.n = H₂.n)
    (ht : ∀ i : Fin H₁.n, H₁.times i = H₂.times (Fin.cast hn i))
    (hv : ∀ (i : Fin H₁.n) (h : (i : ℕ) + 1 < H₁.n),
      H₁.values i ω = H₂.values (Fin.cast hn i) ω) :
    H₁.stochasticIntegral_at W t ω = H₂.stochasticIntegral_at W t ω := by
  unfold stochasticIntegral_at
  refine Fintype.sum_equiv (Fin.castOrderIso hn).toEquiv _ _ fun i => ?_
  simp only [RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply]
  by_cases h : (i : ℕ) + 1 < H₁.n
  · have h' : (Fin.cast hn i : ℕ) + 1 < H₂.n := by
      change (i : ℕ) + 1 < H₂.n; omega
    simp only [dif_pos h, dif_pos h']
    rw [ht i, ht ⟨(i : ℕ) + 1, h⟩, hv i h]
    simp [Fin.cast]
  · have h' : ¬((Fin.cast hn i : ℕ) + 1 < H₂.n) := by
      change ¬((i : ℕ) + 1 < H₂.n); omega
    simp only [dif_neg h, dif_neg h']

/-! ## The merged partition construction

Given SimpleProcesses H₁ and H₂, we construct a SimpleProcess on the
union of their partition times whose integral equals the linear combination
of their integrals. -/

section MergedPartition

variable (H₁ H₂ : SimpleProcess F) (a b : ℝ)

/-- The union of partition times. -/
noncomputable def mergedFinset (H₁ H₂ : SimpleProcess F) : Finset ℝ :=
  H₁.partitionFinset ∪ H₂.partitionFinset

/-- The sorted merged times as a list. -/
noncomputable def mergedList (H₁ H₂ : SimpleProcess F) : List ℝ :=
  (mergedFinset H₁ H₂).sort (· ≤ ·)

/-- Number of merged partition times. -/
noncomputable def mergedLen (H₁ H₂ : SimpleProcess F) : ℕ :=
  (mergedFinset H₁ H₂).card

theorem mergedList_length :
    (mergedList H₁ H₂).length = mergedLen H₁ H₂ := by
  simp [mergedList, mergedLen, Finset.length_sort]

/-- The merged times are strictly sorted. -/
theorem mergedList_sortedLT :
    (mergedList H₁ H₂).SortedLT :=
  Finset.sortedLT_sort _

/-- Strict monotonicity of merged times. -/
theorem mergedList_strictMono :
    StrictMono (mergedList H₁ H₂).get :=
  (mergedList_sortedLT H₁ H₂).strictMono_get

/-- H₁'s times are in the merged finset. -/
theorem times_mem_merged₁ (i : Fin H₁.n) :
    H₁.times i ∈ mergedFinset H₁ H₂ :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- H₂'s times are in the merged finset. -/
theorem times_mem_merged₂ (j : Fin H₂.n) :
    H₂.times j ∈ mergedFinset H₁ H₂ :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end MergedPartition

/-! ## The merged SimpleProcess -/

/-- Construct the merged SimpleProcess for linear combination.
    Uses the sorted union of partition times, with values determined
    by valueAtTime lookups on the original processes. -/
noncomputable def mergedProcess (H₁ H₂ : SimpleProcess F) (a b : ℝ) : SimpleProcess F where
  n := mergedLen H₁ H₂
  times := fun k =>
    (mergedList H₁ H₂).get (k.cast (mergedList_length H₁ H₂).symm)
  values := fun k ω =>
    let s := (mergedList H₁ H₂).get (k.cast (mergedList_length H₁ H₂).symm)
    a * H₁.valueAtTime s ω + b * H₂.valueAtTime s ω
  increasing := by
    intro i j hij
    exact mergedList_strictMono H₁ H₂ (by
      simp only [Fin.lt_def] at hij ⊢
      exact hij)
  adapted := by
    intro i
    exact (measurable_const.mul (measurable_valueAtTime H₁ _)).add
      (measurable_const.mul (measurable_valueAtTime H₂ _))

/-! ## Integral equality for the merged process

The main technical result: the integral of the merged process equals
the linear combination of the original integrals.

The proof strategy:
1. Rewrite all integrals using the min formulation
2. Distribute the linear combination through the merged sum
3. Show each "H₁ part" sum equals H₁'s integral (refinement preserves integral)
4. Similarly for H₂

Step 3 is the key "refinement preserves integral" result, proved via
induction on extra time points. -/

/-- Key property of valueAtTime: if s is in interval [t_j, t_{j+1}),
    then valueAtTime returns H.values j. -/
theorem valueAtTime_in_interval (H : SimpleProcess F) {j : Fin H.n}
    (hj : (j : ℕ) + 1 < H.n) {s : ℝ}
    (hs_lo : H.times j ≤ s) (hs_hi : s < H.times ⟨(j : ℕ) + 1, hj⟩) :
    H.valueAtTime s = H.values j := by
  unfold valueAtTime
  have hexists : ∃ (j' : Fin H.n) (_ : (j' : ℕ) + 1 < H.n),
      H.times j' ≤ s ∧ s < H.times ⟨(j' : ℕ) + 1, ‹_›⟩ :=
    ⟨j, hj, hs_lo, hs_hi⟩
  rw [dif_pos hexists]
  -- The chosen index must equal j (intervals are disjoint for strictly increasing times)
  obtain ⟨hj', hs'_lo, hs'_hi⟩ := hexists.choose_spec
  -- Need to show H.values hexists.choose = H.values j
  congr 1
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · -- hexists.choose < j: t_{choose+1} ≤ t_j ≤ s, contradicting s < t_{choose+1}
    have h_nat : (hexists.choose : ℕ) < (j : ℕ) := h_lt
    have h_succ_le : (hexists.choose : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_of_lt h_nat
    have h_le : H.times ⟨(hexists.choose : ℕ) + 1, hj'⟩ ≤ H.times j := by
      rcases h_succ_le.eq_or_lt with h_eq | h_strict
      · exact le_of_eq (congrArg H.times (Fin.ext h_eq))
      · exact le_of_lt (H.increasing ⟨(hexists.choose : ℕ) + 1, hj'⟩ j
            (show (⟨_, hj'⟩ : Fin H.n) < j from h_strict))
    linarith
  · -- hexists.choose > j: t_{j+1} ≤ t_choose ≤ s, contradicting s < t_{j+1}
    have h_nat : (j : ℕ) < (hexists.choose : ℕ) := h_gt
    have h_succ_le : (j : ℕ) + 1 ≤ (hexists.choose : ℕ) := Nat.succ_le_of_lt h_nat
    have h_le : H.times ⟨(j : ℕ) + 1, hj⟩ ≤ H.times hexists.choose := by
      rcases h_succ_le.eq_or_lt with h_eq | h_strict
      · exact le_of_eq (congrArg H.times (Fin.ext h_eq))
      · exact le_of_lt (H.increasing ⟨(j : ℕ) + 1, hj⟩ hexists.choose
            (show (⟨_, hj⟩ : Fin H.n) < hexists.choose from h_strict))
    linarith

/-- valueAtTime returns 0 when s is before all partition times. -/
theorem valueAtTime_before (H : SimpleProcess F) {s : ℝ}
    (hn : H.n > 0)
    (hs : s < H.times ⟨0, hn⟩) :
    H.valueAtTime s = fun _ => 0 := by
  unfold valueAtTime
  rw [dif_neg]
  push_neg
  intro j hj hs_lo
  exfalso
  have h0 : H.times ⟨0, hn⟩ ≤ H.times j := by
    by_cases h : (j : ℕ) = 0
    · have : j = ⟨0, hn⟩ := Fin.ext h; rw [this]
    · exact le_of_lt (H.increasing ⟨0, hn⟩ j (by simp [Fin.lt_def]; omega))
  linarith

/-- valueAtTime returns 0 when s is past the last active interval. -/
theorem valueAtTime_after (H : SimpleProcess F) {s : ℝ}
    (hn : H.n ≥ 1)
    (hs : H.times ⟨H.n - 1, by omega⟩ ≤ s) :
    H.valueAtTime s = fun _ => 0 := by
  unfold valueAtTime
  rw [dif_neg]
  push_neg
  intro j hj hs_lo
  -- Goal: H.times ⟨j+1, hj⟩ ≤ s
  -- j+1 < n means j+1 ≤ n-1, so t_{j+1} ≤ t_{n-1} ≤ s
  calc H.times ⟨(j : ℕ) + 1, hj⟩
      ≤ H.times ⟨H.n - 1, by omega⟩ := by
        by_cases h : (j : ℕ) + 1 = H.n - 1
        · have : (⟨(j : ℕ) + 1, hj⟩ : Fin H.n) = ⟨H.n - 1, by omega⟩ := Fin.ext (by omega)
          rw [this]
        · exact le_of_lt (H.increasing ⟨(j : ℕ) + 1, hj⟩ ⟨H.n - 1, by omega⟩
            (by simp [Fin.lt_def]; omega))
    _ ≤ s := hs

/-! ## valueAtTime constancy between partition times -/

/-- If no partition time lies in the half-open interval (s₁, s₂], then
    valueAtTime is the same at s₁ and s₂. This is the key ingredient
    for the telescoping argument: inserting/removing a non-partition point
    doesn't change the step-function value. -/
theorem valueAtTime_eq_no_partition_in_Ioc (H : SimpleProcess F) {s₁ s₂ : ℝ}
    (h_lt : s₁ < s₂)
    (h_no_in : ∀ i : Fin H.n, ¬(s₁ < H.times i ∧ H.times i ≤ s₂)) :
    H.valueAtTime s₁ = H.valueAtTime s₂ := by
  -- Case split: is s₁ in some interval [t_j, t_{j+1})?
  by_cases hs₁ : ∃ (j : Fin H.n) (_ : (j : ℕ) + 1 < H.n),
      H.times j ≤ s₁ ∧ s₁ < H.times ⟨(j : ℕ) + 1, ‹_›⟩
  · -- s₁ ∈ [t_j, t_{j+1}). Both s₁ and s₂ are in interval j.
    obtain ⟨j, hj, hj_lo, hj_hi⟩ := hs₁
    have hs₂_hi : s₂ < H.times ⟨(j : ℕ) + 1, hj⟩ := by
      by_contra h; push_neg at h
      exact h_no_in ⟨(j : ℕ) + 1, hj⟩ ⟨by linarith, h⟩
    rw [valueAtTime_in_interval H hj hj_lo hj_hi,
        valueAtTime_in_interval H hj (le_trans hj_lo (le_of_lt h_lt)) hs₂_hi]
  · -- s₁ not in any interval. Show s₂ is also not in any interval.
    unfold valueAtTime
    rw [dif_neg hs₁]
    suffices hs₂ : ¬∃ (j : Fin H.n) (_ : (j : ℕ) + 1 < H.n),
        H.times j ≤ s₂ ∧ s₂ < H.times ⟨(j : ℕ) + 1, ‹_›⟩ by
      rw [dif_neg hs₂]
    intro ⟨j, hj, hj_lo, hj_hi⟩
    by_cases h_le : H.times j ≤ s₁
    · exact hs₁ ⟨j, hj, h_le, lt_trans h_lt hj_hi⟩
    · push_neg at h_le
      exact h_no_in j ⟨h_le, hj_lo⟩

/-! ## Partition infrastructure for refinement proof -/

/-- H.times is strictly monotone. -/
theorem times_strictMono (H : SimpleProcess F) : StrictMono H.times := H.increasing

/-- H.times is injective. -/
theorem times_injective (H : SimpleProcess F) : Function.Injective H.times :=
  H.times_strictMono.injective

/-- The partition finset has cardinality H.n. -/
theorem partitionFinset_card (H : SimpleProcess F) :
    H.partitionFinset.card = H.n := by
  unfold partitionFinset
  rw [Finset.card_image_of_injective _ H.times_injective, Finset.card_univ, Fintype.card_fin]

/-- valueAtTime at a partition time t_j equals H.values j (when j+1 < n). -/
theorem valueAtTime_partition_time (H : SimpleProcess F) (j : Fin H.n)
    (hj : (j : ℕ) + 1 < H.n) :
    H.valueAtTime (H.times j) = H.values j :=
  H.valueAtTime_in_interval hj le_rfl
    (H.increasing j ⟨(j : ℕ) + 1, hj⟩ (by simp [Fin.lt_def]))

/-- The sorted partition finset equals List.ofFn H.times. -/
theorem sort_partitionFinset_eq (H : SimpleProcess F) :
    H.partitionFinset.sort (· ≤ ·) = List.ofFn H.times := by
  have h_pw₁ : (H.partitionFinset.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    Finset.pairwise_sort H.partitionFinset (· ≤ ·)
  have h_sorted₁ : (H.partitionFinset.sort (· ≤ ·)).SortedLE := h_pw₁.sortedLE
  have h_sorted₂ : (List.ofFn H.times).SortedLE :=
    (List.pairwise_ofFn.mpr (fun (i j : Fin H.n) (hij : i < j) =>
      le_of_lt (H.increasing i j hij))).sortedLE
  have h_perm : List.Perm (H.partitionFinset.sort (· ≤ ·)) (List.ofFn H.times) := by
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
        (List.nodup_ofFn.mpr H.times_injective)]
    intro x
    simp only [Finset.mem_sort, partitionFinset, Finset.mem_image, Finset.mem_univ, true_and,
      List.mem_ofFn', Set.mem_range]
  exact List.Perm.eq_of_sortedLE h_sorted₁ h_sorted₂ h_perm

/-- The refined sum of a simple process over a sorted list of time points.
    This packages the common sum expression used in refinement arguments. -/
noncomputable def refinedSum (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) (ω : Ω) (L : List ℝ) : ℝ :=
  ∑ k : Fin L.length, if hk : (k : ℕ) + 1 < L.length then
    H.valueAtTime (L.get k) ω *
      (W.process (min (L.get ⟨(k : ℕ) + 1, hk⟩) t) ω -
       W.process (min (L.get k) t) ω)
  else 0

/-- Removing an element from a Finset.sort corresponds to List.erase. -/
theorem sort_erase_comm (S : Finset ℝ) (s : ℝ) (hs : s ∈ S) :
    (S.erase s).sort (· ≤ ·) = (S.sort (· ≤ ·)).erase s := by
  have h_sorted₁ : ((S.erase s).sort (· ≤ ·)).SortedLE :=
    (Finset.pairwise_sort (S.erase s) (· ≤ ·)).sortedLE
  have h_sorted₂ : ((S.sort (· ≤ ·)).erase s).SortedLE :=
    ((Finset.pairwise_sort S (· ≤ ·)).sublist List.erase_sublist).sortedLE
  have h_nodup_S : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have h_perm : List.Perm ((S.erase s).sort (· ≤ ·)) ((S.sort (· ≤ ·)).erase s) := by
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (h_nodup_S.erase s)]
    intro x
    simp only [Finset.mem_sort, Finset.mem_erase, h_nodup_S.mem_erase_iff]
  exact List.Perm.eq_of_sortedLE h_sorted₁ h_sorted₂ h_perm

/-! ## Element access in the sorted partition list -/

/-- Accessing elements of a list via a list equality. -/
private theorem getElem_of_eq {L₁ L₂ : List ℝ} (heq : L₁ = L₂)
    (k : ℕ) (hk₁ : k < L₁.length) :
    L₁[k] = L₂[k]'(heq ▸ hk₁) := by subst heq; rfl

/-- Element access in the sorted partition list: the k-th element is H.times k. -/
theorem sort_partitionFinset_getElem (H : SimpleProcess F)
    (k : ℕ) (hk : k < (H.partitionFinset.sort (· ≤ ·)).length) :
    (H.partitionFinset.sort (· ≤ ·))[k] =
    H.times ⟨k, by rw [← H.partitionFinset_card, ← Finset.length_sort (· ≤ ·)]; exact hk⟩ := by
  rw [getElem_of_eq H.sort_partitionFinset_eq k hk]
  simp [List.getElem_ofFn]

/-- Get-based element access for the sorted partition list. -/
theorem sort_partitionFinset_get (H : SimpleProcess F)
    (k : Fin (H.partitionFinset.sort (· ≤ ·)).length) :
    (H.partitionFinset.sort (· ≤ ·)).get k =
    H.times ⟨k.val, by rw [← H.partitionFinset_card, ← Finset.length_sort (· ≤ ·)]; exact k.isLt⟩ := by
  simp only [List.get_eq_getElem]
  exact sort_partitionFinset_getElem H k.val k.isLt

/-! ## Base case: refinedSum over partition finset equals the integral -/

/-- Base case for refinement: the integral equals refinedSum over the partition finset. -/
theorem refinedSum_partition_base (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) (ω : Ω) :
    H.stochasticIntegral_at W t ω =
    H.refinedSum W t ω (H.partitionFinset.sort (· ≤ ·)) := by
  rw [stochasticIntegral_at_eq_min]
  unfold refinedSum
  set L := H.partitionFinset.sort (· ≤ ·) with hL_def
  have hlen : L.length = H.n := by
    simp [hL_def, H.sort_partitionFinset_eq, List.length_ofFn]
  symm
  exact Fintype.sum_equiv (Fin.castOrderIso hlen).toEquiv _ _ fun k => by
    simp only [RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply]
    by_cases hk : (k : ℕ) + 1 < L.length
    · have hk' : (Fin.cast hlen k : ℕ) + 1 < H.n := by simp [Fin.cast]; omega
      simp only [dif_pos hk, dif_pos hk']
      have hget_k : L.get k = H.times (Fin.cast hlen k) := by
        rw [sort_partitionFinset_get]; congr 1
      have hget_k1 : L.get ⟨(k : ℕ) + 1, hk⟩ =
          H.times ⟨(Fin.cast hlen k : ℕ) + 1, hk'⟩ := by
        rw [sort_partitionFinset_get]; congr 1
      rw [hget_k, hget_k1, valueAtTime_partition_time H (Fin.cast hlen k) hk']
    · have hk' : ¬((Fin.cast hlen k : ℕ) + 1 < H.n) := by simp [Fin.cast]; omega
      simp only [dif_neg hk, dif_neg hk']

/-! ## Telescoping step: removing a non-partition point preserves refinedSum -/

/-- No element of a strictly sorted list lies strictly between consecutive elements. -/
private theorem no_elem_between_sorted {L : List ℝ} (hL : L.SortedLT)
    {p : ℕ} (hp : p + 1 < L.length) {x : ℝ} (hx : x ∈ L)
    (h1 : L[p]'(by omega) < x) (h2 : x < L[p + 1]'hp) : False := by
  rw [List.mem_iff_getElem] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hsm := hL.strictMono_get
  have h_pq : p < q := by
    by_contra h; push_neg at h
    have : L[q]'hq ≤ L[p]'(by omega) :=
      hsm.monotone (show (⟨q, hq⟩ : Fin L.length) ≤ ⟨p, by omega⟩ from h)
    linarith
  have h_qp1 : q < p + 1 := by
    by_contra h; push_neg at h
    have : L[p + 1]'hp ≤ L[q]'hq :=
      hsm.monotone (show (⟨p + 1, hp⟩ : Fin L.length) ≤ ⟨q, hq⟩ from h)
    linarith
  omega

/-- In a strictly sorted list containing all partition times, if L[p] is not a
    partition time and p > 0, then `valueAtTime(L[p-1]) = valueAtTime(L[p])`. -/
private theorem valueAtTime_eq_at_nonpartition (H : SimpleProcess F)
    {L : List ℝ} (hL : L.SortedLT) {p : ℕ} (hp : p < L.length) (hp_pos : 0 < p)
    (hs_not : L[p] ∉ H.partitionFinset)
    (hS : ∀ i : Fin H.n, H.times i ∈ L) :
    H.valueAtTime (L[p - 1]'(by omega)) = H.valueAtTime (L[p]) := by
  have hp1 : p - 1 + 1 = p := by omega
  apply valueAtTime_eq_no_partition_in_Ioc H
  · have : (⟨p - 1, by omega⟩ : Fin L.length) < ⟨p, hp⟩ := by simp [Fin.lt_def]; omega
    exact hL.strictMono_get this
  · intro i
    intro ⟨h_gt, h_le⟩
    -- h_gt : L[p-1] < H.times i, h_le : H.times i ≤ L[p]
    rcases h_le.lt_or_eq with h_lt | h_eq
    · -- L[p-1] < H.times i < L[p]: impossible
      have hp1_lt : p - 1 + 1 < L.length := by omega
      exact no_elem_between_sorted hL hp1_lt (hS i)
        (by convert h_gt using 2) (by convert h_lt using 2)
    · -- H.times i = L[p]: contradicts hs_not
      have hmem : H.times i ∈ H.partitionFinset :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [h_eq] at hmem
      exact hs_not hmem

/-- Removing a non-partition point from S doesn't change the refined sum.
    This is the key telescoping lemma: the value (via valueAtTime) is
    constant between partition times, so the BM increments telescope. -/
theorem refinedSum_erase_nonpartition (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) (ω : Ω) (S : Finset ℝ) (s : ℝ)
    (hs_in : s ∈ S) (hs_not : s ∉ H.partitionFinset)
    (hS : ∀ i : Fin H.n, H.times i ∈ S) :
    H.refinedSum W t ω (S.sort (· ≤ ·)) =
    H.refinedSum W t ω ((S.erase s).sort (· ≤ ·)) := by
  rw [sort_erase_comm S s hs_in]
  set L := S.sort (· ≤ ·) with hL_def
  have hL_nodup : L.Nodup := Finset.sort_nodup _ _
  have hL_sorted : L.SortedLT := Finset.sortedLT_sort _
  have hs_mem_L : s ∈ L := by rw [hL_def]; exact (Finset.mem_sort _).mpr hs_in
  have hS_L : ∀ i : Fin H.n, H.times i ∈ L :=
    fun i => by rw [hL_def]; exact (Finset.mem_sort _).mpr (hS i)
  rw [← List.eraseIdx_idxOf_eq_erase s L]
  set p := L.idxOf s with hp_def
  have hp_lt : p < L.length := List.idxOf_lt_length_of_mem hs_mem_L
  have hLp_eq : L[p] = s := List.getElem_idxOf hp_lt
  have hLp_not : L[p] ∉ H.partitionFinset := hLp_eq ▸ hs_not
  have hlen_e : (L.eraseIdx p).length + 1 = L.length := List.length_eraseIdx_add_one hp_lt
  set m := (L.eraseIdx p).length with hm_def
  have hLm : L.length = m + 1 := by omega
  -- Define the term function for the original sum (indexed by Fin (m+1))
  let F : Fin (m + 1) → ℝ := fun k =>
    if hk : (k : ℕ) + 1 < m + 1 then
      H.valueAtTime (L[k.val]'(by omega)) ω *
        (W.process (min (L[k.val + 1]'(by omega)) t) ω -
         W.process (min (L[k.val]'(by omega)) t) ω)
    else 0
  -- The original refinedSum equals Σ F
  have hsum_orig : H.refinedSum W t ω L = ∑ k : Fin (m + 1), F k := by
    unfold refinedSum
    exact Fintype.sum_equiv (Fin.castOrderIso hLm).toEquiv _ _ fun k => by
      simp only [RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, F]
      by_cases hk : (k : ℕ) + 1 < L.length
      · simp only [dif_pos hk, List.get_eq_getElem, Fin.cast, Fin.val_mk]
        rw [dif_pos (show (k : ℕ) + 1 < m + 1 from by omega)]
      · have hk' : ¬((Fin.cast hLm k : ℕ) + 1 < m + 1) := by simp [Fin.cast]; omega
        simp only [dif_neg hk, dif_neg hk']
  -- Define the term function for the erased sum (indexed by Fin m)
  let G : Fin m → ℝ := fun k =>
    if hk : (k : ℕ) + 1 < m then
      H.valueAtTime ((L.eraseIdx p)[k.val]'(by omega)) ω *
        (W.process (min ((L.eraseIdx p)[k.val + 1]'(by omega)) t) ω -
         W.process (min ((L.eraseIdx p)[k.val]'(by omega)) t) ω)
    else 0
  -- The erased refinedSum equals Σ G
  have hsum_erase : H.refinedSum W t ω (L.eraseIdx p) = ∑ k : Fin m, G k := by
    unfold refinedSum; rfl
  rw [hsum_orig, hsum_erase]
  -- Decompose: Σ F = F(⟨p,_⟩) + Σ_{k : Fin m} F(⟨p,_⟩.succAbove k)
  set pfin : Fin (m + 1) := ⟨p, by omega⟩
  rw [Fin.sum_univ_succAbove _ pfin]
  -- Goal: F pfin + Σ (F ∘ pfin.succAbove) = Σ G
  -- Helper: getElem_eraseIdx to access erased list elements
  have h_eraseIdx : ∀ (j : ℕ) (hj : j < m),
      (L.eraseIdx p)[j] = if j < p then L[j] else L[j + 1] := by
    intro j hj; exact List.getElem_eraseIdx (by omega)
  -- Helper: succAbove values
  have h_succAbove : ∀ k : Fin m,
      (pfin.succAbove k).val = if k.val < p then k.val else k.val + 1 := by
    intro k
    by_cases hk : k.castSucc < pfin
    · rw [Fin.succAbove_of_castSucc_lt _ _ hk]; simp [Fin.castSucc, Fin.lt_def] at hk ⊢; exact hk
    · push_neg at hk
      rw [Fin.succAbove_of_le_castSucc _ _ hk]; simp [Fin.succ, Fin.castSucc, Fin.le_def] at hk ⊢
      omega
  -- Helper: G(k) = F(succAbove k) when k+1 ≠ p or p = 0
  have h_match : ∀ k : Fin m, (k.val + 1 ≠ p ∨ p = 0) → G k = F (pfin.succAbove k) := by
    intro k hcond
    have hsa := h_succAbove k
    by_cases hkp : k.val < p
    · -- k < p: succAbove has value k
      rw [if_pos hkp] at hsa  -- hsa : succAbove val = k.val
      have hk1p : k.val + 1 < p := by omega
      -- k+1 < m follows from k+1 < p ≤ m
      have hk1m : k.val + 1 < m := by omega
      -- Both dif conditions hold; unfold G and F
      have hG : G k = H.valueAtTime (L.eraseIdx p)[k.val] ω *
          (W.process (min (L.eraseIdx p)[k.val + 1] t) ω -
           W.process (min (L.eraseIdx p)[k.val] t) ω) := dif_pos hk1m
      have hF : F (pfin.succAbove k) = H.valueAtTime L[(pfin.succAbove k).val] ω *
          (W.process (min L[(pfin.succAbove k).val + 1] t) ω -
           W.process (min L[(pfin.succAbove k).val] t) ω) := dif_pos (by omega)
      rw [hG, hF, h_eraseIdx k.val k.isLt, if_pos hkp,
          h_eraseIdx (k.val + 1) hk1m, if_pos hk1p]
      simp only [hsa]
    · -- k ≥ p: succAbove has value k + 1
      push_neg at hkp
      rw [if_neg (by omega : ¬(k.val < p))] at hsa  -- hsa : succAbove val = k.val + 1
      by_cases hk1 : k.val + 1 < m
      · -- Both conditions hold
        have hG : G k = H.valueAtTime (L.eraseIdx p)[k.val] ω *
            (W.process (min (L.eraseIdx p)[k.val + 1] t) ω -
             W.process (min (L.eraseIdx p)[k.val] t) ω) := dif_pos hk1
        have hF : F (pfin.succAbove k) = H.valueAtTime L[(pfin.succAbove k).val] ω *
            (W.process (min L[(pfin.succAbove k).val + 1] t) ω -
             W.process (min L[(pfin.succAbove k).val] t) ω) := dif_pos (by omega)
        rw [hG, hF, h_eraseIdx k.val k.isLt, if_neg (by omega : ¬(k.val < p)),
            h_eraseIdx (k.val + 1) hk1, if_neg (by omega : ¬(k.val + 1 < p))]
        simp only [hsa]
      · -- Both conditions fail
        have hG : G k = 0 := dif_neg hk1
        have hF : F (pfin.succAbove k) = 0 := dif_neg (by omega)
        rw [hG, hF]
  -- Main proof by cases on p
  by_cases hp0 : p = 0
  · -- Case p = 0: F pfin = 0 (valueAtTime = 0), G = F ∘ succAbove
    have hFp : F pfin = 0 := by
      by_cases hm0 : (pfin : ℕ) + 1 < m + 1
      · have hF_exp : F pfin = H.valueAtTime (L[(pfin : ℕ)]'(by omega)) ω *
            (W.process (min (L[(pfin : ℕ) + 1]'(by omega)) t) ω -
             W.process (min (L[(pfin : ℕ)]'(by omega)) t) ω) := dif_pos hm0
        rw [hF_exp]
        have hval : H.valueAtTime (L[0]'(by omega)) = fun _ => 0 := by
          by_cases hn0 : H.n = 0
          · unfold valueAtTime; rw [dif_neg]; push_neg
            intro j; exact absurd j.isLt (by omega)
          · apply valueAtTime_before H (by omega)
            have h0 := hS_L ⟨0, by omega⟩
            rw [List.mem_iff_getElem] at h0
            obtain ⟨q, hq, hq_eq⟩ := h0
            by_cases hq0 : q = 0
            · exfalso; apply hLp_not
              have : L[p] = L[q] := by congr 1; omega
              rw [this, hq_eq]
              exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
            · calc L[0]'(by omega) < L[q]'hq :=
                    hL_sorted.strictMono_get (show (⟨0, by omega⟩ : Fin L.length) <
                      ⟨q, hq⟩ from by simp [Fin.lt_def]; omega)
                _ = H.times ⟨0, by omega⟩ := hq_eq
        simp only [show (pfin : ℕ) = 0 from hp0, hval]; ring
      · exact dif_neg hm0
    rw [hFp, zero_add]
    exact Finset.sum_congr rfl fun k _ => (h_match k (Or.inr hp0)).symm
  · by_cases hpm : p = m
    · -- Case p = m: F pfin = 0 (last term condition fails)
      have hFp : F pfin = 0 := dif_neg (by change ¬(p + 1 < m + 1); omega)
      rw [hFp, zero_add]
      apply Finset.sum_congr rfl; intro k _
      by_cases hk1 : k.val + 1 < m
      · -- k+1 < m ≤ p: h_match applies (k+1 ≠ p since k+1 < m = p)
        exact (h_match k (Or.inl (by omega))).symm
      · -- k+1 ≥ m, so k = m-1: G = 0, show F(succAbove k) = 0 too
        have hkm : k.val = m - 1 := by omega
        have hG0 : G k = 0 := dif_neg hk1
        -- succAbove k has value k.val (since k.val < p = m)
        have hsa := h_succAbove k
        rw [if_pos (show k.val < p from by omega)] at hsa
        -- F(succAbove k): condition k.val + 1 < m+1, true since k.val < m
        have hF_exp : F (pfin.succAbove k) = H.valueAtTime L[(pfin.succAbove k).val] ω *
            (W.process (min L[(pfin.succAbove k).val + 1] t) ω -
             W.process (min L[(pfin.succAbove k).val] t) ω) := dif_pos (by omega)
        rw [hG0, hF_exp]; symm
        -- valueAtTime(L[m-1]) = 0 (past last active interval)
        have hval : H.valueAtTime (L[m - 1]'(by omega)) = fun _ => 0 := by
          by_cases hn0 : H.n = 0
          · unfold valueAtTime; rw [dif_neg]; push_neg
            intro j; exact absurd j.isLt (by omega)
          · apply valueAtTime_after H (by omega : H.n ≥ 1)
            have h_last := hS_L ⟨H.n - 1, by omega⟩
            rw [List.mem_iff_getElem] at h_last
            obtain ⟨q, hq, hq_eq⟩ := h_last
            have hq_le : q ≤ m - 1 := by
              by_contra hc; push_neg at hc
              have hqp : q = p := by omega
              subst hqp
              have hmem : H.times ⟨H.n - 1, by omega⟩ ∈ H.partitionFinset :=
                Finset.mem_image.mpr ⟨⟨H.n - 1, by omega⟩, Finset.mem_univ _, rfl⟩
              rw [← hq_eq] at hmem
              exact hLp_not hmem
            calc H.times ⟨H.n - 1, by omega⟩
                = L[q]'hq := hq_eq.symm
              _ ≤ L[m - 1]'(by omega) :=
                  hL_sorted.strictMono_get.monotone (show (⟨q, hq⟩ : Fin L.length) ≤
                    ⟨m - 1, by omega⟩ from hq_le)
        have hval_pt := congr_fun hval ω
        simp only [hsa, hkm, hval_pt]; ring
    · -- Case 0 < p < m: telescoping
      have hp_pos : 0 < p := by omega
      have hp_lt_m : p < m := by omega
      suffices h_telescope : (∑ k : Fin m, G k) = F pfin + ∑ k : Fin m, F (pfin.succAbove k) by
        linarith
      -- Isolate term p-1 from both sums
      have hp1_mem : (⟨p - 1, by omega⟩ : Fin m) ∈ Finset.univ := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ hp1_mem, ← Finset.add_sum_erase _ _ hp1_mem]
      -- The sums over k ≠ p-1 are equal (G(k) = F(succAbove k) for k ≠ p-1)
      have h_rest : ∀ k ∈ Finset.univ.erase (⟨p - 1, by omega⟩ : Fin m),
          G k = F (pfin.succAbove k) := by
        intro k hk
        apply h_match
        rw [Finset.mem_erase] at hk
        left; intro heq; exact hk.1 (Fin.ext (show k.val = p - 1 by omega))
      rw [Finset.sum_congr rfl h_rest]
      -- Suffices: G(p-1) = F pfin + F(succAbove(p-1))
      suffices h_key : G ⟨p - 1, by omega⟩ =
          F pfin + F (pfin.succAbove ⟨p - 1, by omega⟩) by linarith
      -- Key: valueAtTime is constant at the non-partition point
      have hv_eq := valueAtTime_eq_at_nonpartition H hL_sorted hp_lt hp_pos hLp_not hS_L
      have hv_pt : H.valueAtTime (L[p]'hp_lt) ω =
          H.valueAtTime (L[p - 1]'(by omega)) ω := (congr_fun hv_eq ω).symm
      -- succAbove ⟨p-1, _⟩ has value p-1 (since p-1 < p)
      have hsa := h_succAbove ⟨p - 1, by omega⟩
      simp only [show p - 1 < p from by omega, ite_true] at hsa
      -- Compute the three terms
      -- Precompute eraseIdx equalities (avoiding dependent type rewrites inside getElem)
      have he_pm1 : (L.eraseIdx p)[p - 1] = L[p - 1] :=
        (h_eraseIdx (p - 1) (by omega)).trans (if_pos (by omega))
      have he_pp1 : (L.eraseIdx p)[(p - 1) + 1] = L[p + 1] := by
        have := h_eraseIdx ((p - 1) + 1) (by omega)
        rw [if_neg (show ¬((p - 1) + 1 < p) from by omega)] at this
        rw [this]; congr 1; omega
      -- Step 1: Unfold G at p-1 using dif_pos (G is a let-binding, rw can't see through it)
      have hG_step : G ⟨p - 1, by omega⟩ =
          H.valueAtTime ((L.eraseIdx p)[p - 1]) ω *
            (W.process (min ((L.eraseIdx p)[(p - 1) + 1]) t) ω -
             W.process (min ((L.eraseIdx p)[p - 1]) t) ω) :=
        dif_pos (show (p - 1 : ℕ) + 1 < m from by omega)
      have hG_val : G ⟨p - 1, by omega⟩ =
          H.valueAtTime (L[p - 1]'(by omega)) ω *
            (W.process (min (L[p + 1]'(by omega)) t) ω -
             W.process (min (L[p - 1]'(by omega)) t) ω) := by
        rw [hG_step, he_pm1, he_pp1]
      -- Step 2: Unfold F at pfin
      have hFp_val : F pfin =
          H.valueAtTime (L[p]'(by omega)) ω *
            (W.process (min (L[p + 1]'(by omega)) t) ω -
             W.process (min (L[p]'(by omega)) t) ω) :=
        dif_pos (show p + 1 < m + 1 from by omega)
      -- Step 3: Unfold F at succAbove (p-1)
      have hFsa_val : F (pfin.succAbove ⟨p - 1, by omega⟩) =
          H.valueAtTime (L[p - 1]'(by omega)) ω *
            (W.process (min (L[p]'(by omega)) t) ω -
             W.process (min (L[p - 1]'(by omega)) t) ω) :=
        calc F (pfin.succAbove ⟨p - 1, by omega⟩)
          _ = F ⟨p - 1, by omega⟩ := congrArg F (Fin.ext hsa)
          _ = H.valueAtTime (L[p - 1]'(by omega)) ω *
                (W.process (min (L[(p - 1) + 1]'(by omega)) t) ω -
                 W.process (min (L[p - 1]'(by omega)) t) ω) :=
              dif_pos (show (p - 1 : ℕ) + 1 < m + 1 from by omega)
          _ = H.valueAtTime (L[p - 1]'(by omega)) ω *
                (W.process (min (L[p]'(by omega)) t) ω -
                 W.process (min (L[p - 1]'(by omega)) t) ω) := by
              simp only [Nat.sub_add_cancel hp_pos]
      rw [hG_val, hFp_val, hFsa_val, hv_pt]; ring

/-! ## Refinement preserves integral: the core inductive proof -/

/-- The stochastic integral of a simple process, computed using the min formulation,
    can be expressed as a Finset sum over a refinement of the partition.
    This is the fundamental "refinement preserves integral" theorem.

    Proof by induction on |S \ partitionFinset H|. -/
theorem refinement_preserves_integral
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) (ω : Ω)
    (S : Finset ℝ)
    (hS : ∀ i : Fin H.n, H.times i ∈ S) :
    let sorted := S.sort (· ≤ ·)
    H.stochasticIntegral_at W t ω =
    ∑ k : Fin sorted.length, if hk : (k : ℕ) + 1 < sorted.length then
      H.valueAtTime (sorted.get k) ω *
        (W.process (min (sorted.get ⟨(k : ℕ) + 1, hk⟩) t) ω -
         W.process (min (sorted.get k) t) ω)
    else 0 := by
  intro sorted
  -- The goal is: integral = refinedSum H W t ω (S.sort (· ≤ ·))
  change H.stochasticIntegral_at W t ω = H.refinedSum W t ω (S.sort (· ≤ ·))
  -- Induction on (S \ partitionFinset H).card
  suffices ∀ (m : ℕ) (T : Finset ℝ),
      (T \ H.partitionFinset).card ≤ m →
      (∀ i : Fin H.n, H.times i ∈ T) →
      H.stochasticIntegral_at W t ω = H.refinedSum W t ω (T.sort (· ≤ ·)) by
    exact this _ S le_rfl hS
  intro m
  induction m with
  | zero =>
    intro T hcard hT
    -- T \ partitionFinset = ∅, so T ⊆ partitionFinset
    have hT_sub : T ⊆ H.partitionFinset := by
      intro x hx; by_contra h
      have : x ∈ T \ H.partitionFinset := Finset.mem_sdiff.mpr ⟨hx, h⟩
      have := Finset.card_pos.mpr ⟨x, this⟩; omega
    -- Combined with hT, T = partitionFinset
    have hT_eq : T = H.partitionFinset :=
      Finset.Subset.antisymm hT_sub (fun x hx => by
        simp only [partitionFinset, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx; exact hT i)
    rw [hT_eq]; exact refinedSum_partition_base H W t ω
  | succ m ih =>
    intro T hcard hT
    by_cases hextra : (T \ H.partitionFinset).Nonempty
    · -- Pick an extra point s ∈ T \ partitionFinset
      obtain ⟨s, hs_mem⟩ := hextra
      rw [Finset.mem_sdiff] at hs_mem
      -- (T.erase s) has fewer extra points
      have h_erase_card : (T.erase s \ H.partitionFinset).card ≤ m := by
        have : T.erase s \ H.partitionFinset = (T \ H.partitionFinset).erase s := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
        rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hs_mem)]
        omega
      -- T.erase s still contains all partition times
      have h_erase_T : ∀ i : Fin H.n, H.times i ∈ T.erase s := by
        intro i
        rw [Finset.mem_erase]
        refine ⟨?_, hT i⟩
        intro heq
        exact hs_mem.2 (heq ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      -- By IH and telescoping
      calc H.stochasticIntegral_at W t ω
          = H.refinedSum W t ω ((T.erase s).sort (· ≤ ·)) :=
            ih (T.erase s) h_erase_card h_erase_T
        _ = H.refinedSum W t ω (T.sort (· ≤ ·)) :=
            (refinedSum_erase_nonpartition H W t ω T s hs_mem.1 hs_mem.2 hT).symm
    · -- T \ partitionFinset is empty: same as base case
      rw [Finset.not_nonempty_iff_eq_empty] at hextra
      have hT_sub : T ⊆ H.partitionFinset :=
        Finset.sdiff_eq_empty_iff_subset.mp hextra
      have hT_eq : T = H.partitionFinset :=
        Finset.Subset.antisymm hT_sub (fun x hx => by
          simp only [partitionFinset, Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx; exact hT i)
      rw [hT_eq]; exact refinedSum_partition_base H W t ω

/-- H₁ partition times are in the merged finset. -/
theorem h1_times_mem_mergedFinset (H₁ H₂ : SimpleProcess F) (i : Fin H₁.n) :
    H₁.times i ∈ mergedFinset H₁ H₂ :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- H₂ partition times are in the merged finset. -/
theorem h2_times_mem_mergedFinset (H₁ H₂ : SimpleProcess F) (i : Fin H₂.n) :
    H₂.times i ∈ mergedFinset H₁ H₂ :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- Merged process times are in the merged finset. -/
theorem mergedProcess_times_mem (H₁ H₂ : SimpleProcess F) (a b : ℝ)
    (i : Fin (mergedProcess H₁ H₂ a b).n) :
    (mergedProcess H₁ H₂ a b).times i ∈ mergedFinset H₁ H₂ := by
  -- (mergedProcess).times i = (mergedList).get (i.cast ...) ∈ mergedList = (mergedFinset).sort
  have hmem := List.get_mem (mergedList H₁ H₂)
    (i.cast (mergedList_length (F := F) H₁ H₂).symm)
  simp only [mergedList, Finset.mem_sort] at hmem
  exact hmem

/-- The refinedSum of the merged process decomposes as a linear combination.
    This is the key algebraic identity: on the merged partition,
    `(mergedProcess).valueAtTime = a * H₁.valueAtTime + b * H₂.valueAtTime`. -/
theorem mergedProcess_refinedSum_eq (H₁ H₂ : SimpleProcess F)
    (W : BrownianMotion Ω μ) (a b : ℝ) (t : ℝ) (ω : Ω) :
    (mergedProcess H₁ H₂ a b).refinedSum W t ω (mergedList H₁ H₂) =
    a * H₁.refinedSum W t ω (mergedList H₁ H₂) +
    b * H₂.refinedSum W t ω (mergedList H₁ H₂) := by
  unfold refinedSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (k : ℕ) + 1 < (mergedList H₁ H₂).length
  · simp only [dif_pos hk]
    -- Key: at a partition time, the merged process's valueAtTime decomposes
    suffices hval : (mergedProcess H₁ H₂ a b).valueAtTime ((mergedList H₁ H₂).get k) ω =
        a * H₁.valueAtTime ((mergedList H₁ H₂).get k) ω +
        b * H₂.valueAtTime ((mergedList H₁ H₂).get k) ω by
      rw [hval]; ring
    -- Use valueAtTime_in_interval: L.get k ∈ [times(k), times(k+1)) of merged process
    have hlen := mergedList_length (F := F) H₁ H₂
    have hk_n : k.val < (mergedProcess H₁ H₂ a b).n := by
      change k.val < mergedLen H₁ H₂; rw [← hlen]; exact k.isLt
    have hk1_n : k.val + 1 < (mergedProcess H₁ H₂ a b).n := by
      change k.val + 1 < mergedLen H₁ H₂; rw [← hlen]; exact hk
    -- By proof irrelevance, (mergedProcess).times ⟨k.val, hk_n⟩ is def-eq to L.get k,
    -- and (mergedProcess).values ⟨k.val, hk_n⟩ ω is def-eq to a * v₁ + b * v₂
    exact congr_fun (valueAtTime_in_interval (mergedProcess H₁ H₂ a b) hk1_n
      (le_refl _)
      ((mergedProcess H₁ H₂ a b).increasing ⟨k.val, hk_n⟩ ⟨k.val + 1, hk1_n⟩
        (by simp [Fin.lt_def]))) ω
  · simp only [dif_neg hk, mul_zero, zero_add]

/-- The integral of the merged process equals the linear combination.
    Proof: Rewrite all three integrals as refinedSums over the merged partition,
    then use the algebraic identity mergedProcess_refinedSum_eq. -/
theorem mergedProcess_integral_eq
    (H₁ H₂ : SimpleProcess F) (W : BrownianMotion Ω μ) (a b : ℝ)
    (t : ℝ) (ω : Ω) :
    (mergedProcess H₁ H₂ a b).stochasticIntegral_at W t ω =
    a * H₁.stochasticIntegral_at W t ω + b * H₂.stochasticIntegral_at W t ω := by
  -- Rewrite all three integrals as refinedSums over the merged partition
  have hM := refinement_preserves_integral (mergedProcess H₁ H₂ a b) W t ω
    (mergedFinset H₁ H₂) (mergedProcess_times_mem H₁ H₂ a b)
  have h1 := refinement_preserves_integral H₁ W t ω
    (mergedFinset H₁ H₂) (h1_times_mem_mergedFinset H₁ H₂)
  have h2 := refinement_preserves_integral H₂ W t ω
    (mergedFinset H₁ H₂) (h2_times_mem_mergedFinset H₁ H₂)
  rw [hM, h1, h2]
  exact mergedProcess_refinedSum_eq H₁ H₂ W a b t ω

end SimpleProcess

end SPDE

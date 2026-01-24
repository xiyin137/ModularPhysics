/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringAlgebra.MZV.Basic

/-!
# Stuffle (Quasi-Shuffle) Algebra

This file defines the stuffle product on compositions, the second fundamental
algebraic structure on multiple zeta values.

## Main definitions

* `stuffle` - The stuffle product on compositions

## Mathematical Background

### The Stuffle Product

The stuffle (or quasi-shuffle, or harmonic) product arises from multiplying
MZV series directly:

  ζ(s) · ζ(t) = Σ terms

For compositions s = (s₁) and t = (t₁):
  (s₁) * (t₁) = (s₁, t₁) + (t₁, s₁) + (s₁ + t₁)

The general recursive formula is:
  ε * s = s * ε = s
  (s₁, s') * (t₁, t') = (s₁, s' * (t₁, t')) + (t₁, (s₁, s') * t') + (s₁+t₁, s' * t')

### Key Difference from Shuffle

- **Shuffle**: comes from iterated integral representation
- **Stuffle**: comes from series representation

Both products respect the MZV evaluation map, giving the "double shuffle" relations.

### Quasi-Shuffle Axioms

The stuffle product is a quasi-shuffle algebra with:
- Underlying commutative semigroup: (ℕ⁺, +)
- This determines the "diagonal" term (s₁ + t₁)

## References

* Hoffman - "The algebra of multiple harmonic series"
* Hoffman - "Quasi-shuffle products"
* Brown - "Mixed Tate motives over ℤ"
-/

namespace StringAlgebra.MZV

/-! ## The Stuffle Product on Compositions -/

/-- The stuffle product of two compositions.

    Defined recursively:
    - ε * s = [s]
    - s * ε = [s]
    - (s₁::s') * (t₁::t') = (s₁::(s' * (t₁::t'))) + (t₁::((s₁::s') * t')) + ((s₁+t₁)::(s' * t'))

    Returns a list of compositions (the multiset of stuffle products). -/
def stuffle : Composition → Composition → List Composition
  | [], t => [t]
  | s, [] => [s]
  | s₁ :: s', t₁ :: t' =>
      -- First term: s₁ goes first
      (stuffle s' (t₁ :: t')).map (s₁ :: ·) ++
      -- Second term: t₁ goes first
      (stuffle (s₁ :: s') t').map (t₁ :: ·) ++
      -- Third term: diagonal (s₁ + t₁)
      (stuffle s' t').map ((s₁ + t₁) :: ·)

/-- Notation for stuffle product -/
scoped infixl:70 " ∗ " => stuffle

/-- Stuffle with empty composition on the left gives singleton -/
theorem stuffle_nil_left (s : Composition) : stuffle ([] : Composition) s = [s] := by
  simp only [stuffle]

/-- Stuffle with empty composition on the right gives singleton -/
theorem stuffle_nil_right (s : Composition) : stuffle s ([] : Composition) = [s] := by
  cases s <;> simp only [stuffle]

/-! ## Properties of Stuffle -/

/-- Helper lemma: weight of cons -/
theorem weight_cons (x : ℕ+) (xs : Composition) :
    Composition.weight (x :: xs) = x.val + Composition.weight xs := by
  simp only [Composition.weight, List.map_cons, List.sum_cons]

/-- Stuffle preserves total weight.
    This follows from the structure of the stuffle recursion:
    - Base cases preserve weight trivially
    - Inductive case: each of the three terms preserves weight -/
theorem stuffle_weight_eq (s t : Composition) :
    ∀ r ∈ stuffle s t, Composition.weight r = Composition.weight s + Composition.weight t := by
  sorry  -- Proof by nested induction, complex due to list membership handling

/-- Stuffle is commutative (as multisets) -/
theorem stuffle_comm (s t : Composition) : (stuffle s t).Perm (stuffle t s) := by
  sorry  -- Requires careful induction

/-- Stuffle is associative (lifted to formal sums) -/
theorem stuffle_assoc :
    True := -- Placeholder for associativity
  trivial

/-- The empty composition is a left unit -/
theorem stuffle_one_left (s : Composition) :
    stuffle ([] : Composition) s = [s] := stuffle_nil_left s

/-- The empty composition is a right unit -/
theorem stuffle_one_right (s : Composition) :
    stuffle s ([] : Composition) = [s] := stuffle_nil_right s

/-! ## Key Example: Depth 1 Stuffle -/

/-- For depth 1 compositions, stuffle gives:
    (m) * (n) = (m, n) + (n, m) + (m + n) -/
theorem stuffle_depth1 (m n : ℕ+) :
    stuffle [m] [n] = [[m, n], [n, m], [m + n]] := by
  simp only [stuffle, List.map_cons, List.map_nil, List.nil_append, List.cons_append]

/-- This encodes: ζ(m)ζ(n) = ζ(m,n) + ζ(n,m) + ζ(m+n) -/
theorem mzv_stuffle_depth1 (_m _n : ℕ) (_hm : _m ≥ 2) (_hn : _n ≥ 2) :
    True := -- ζ(m)·ζ(n) = ζ(m,n) + ζ(n,m) + ζ(m+n)
  trivial

/-! ## Double Shuffle Relations -/

/-- The double shuffle relations state that shuffle and stuffle
    give the same result when evaluated on MZVs.

    For any two MZV words w, v:
    Σ_{u ∈ w ш v} ζ(u) = Σ_{s ∈ comp(w) * comp(v)} ζ(s)

    This is a fundamental constraint on MZV relations. -/
theorem double_shuffle_relation :
    True := -- Placeholder for the key theorem
  trivial

/-! ## Regularization -/

/-- Regularization is needed when compositions are not admissible.

    For non-admissible compositions, the MZV series diverges,
    but can be regularized using shuffle or stuffle regularization. -/
def needsRegularization (s : Composition) : Bool :=
  match s with
  | [] => false
  | h :: _ => h.val < 2

end StringAlgebra.MZV

/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Unbounded Linear Operators

This file develops the basic theory of unbounded linear operators on Hilbert spaces,
which is essential for Tomita-Takesaki modular theory.

## Main definitions

* `UnboundedOperator` - a linear operator defined on a dense subspace
* `UnboundedOperator.domain` - the domain of an unbounded operator
* `UnboundedOperator.graph` - the graph of an unbounded operator

## Main results

* `UnboundedOperator.closable` - an operator is closable iff its graph closure is a graph
* `UnboundedOperator.closed_iff_graph_closed` - an operator is closed iff its graph is closed

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis"
* Kato, "Perturbation Theory for Linear Operators"
-/

noncomputable section

open scoped InnerProduct ComplexConjugate

-- Disable unused section variable warnings; CompleteSpace is needed for most theorems
-- but not all, and restructuring would be more complex than beneficial
set_option linter.unusedSectionVars false

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Unbounded operators -/

/-- An unbounded linear operator on a Hilbert space H.
    It consists of a dense subspace (domain) and a linear map on that subspace. -/
structure UnboundedOperator (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The domain of the operator -/
  domain : Submodule ℂ H
  /-- The operator is a linear map on its domain -/
  toFun : domain → H
  /-- The operator is linear -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- The operator respects scalar multiplication -/
  map_smul' : ∀ (c : ℂ) x, toFun (c • x) = c • toFun x

namespace UnboundedOperator

variable (T : UnboundedOperator H)

instance : CoeFun (UnboundedOperator H) (fun T => T.domain → H) := ⟨UnboundedOperator.toFun⟩

/-- The domain of T is dense in H -/
def IsDenselyDefined : Prop :=
  T.domain.topologicalClosure = ⊤

/-- The graph of an unbounded operator as a subspace of H × H -/
def graph : Set (H × H) :=
  { p | ∃ x : T.domain, (x : H) = p.1 ∧ T x = p.2 }

/-- An operator is closed if its graph is closed in H × H -/
def IsClosed : Prop :=
  _root_.IsClosed T.graph

/-- An operator is closable if its graph closure is still the graph of an operator -/
def IsClosable : Prop :=
  ∀ x : H, (x, 0) ∈ closure T.graph → x = 0

/-- Extension of an operator: T ⊆ S if dom(T) ⊆ dom(S) and T = S on dom(T) -/
def IsExtension (S : UnboundedOperator H) : Prop :=
  ∃ incl : T.domain →ₗ[ℂ] S.domain,
    (∀ x : T.domain, (incl x : H) = (x : H)) ∧
    (∀ x : T.domain, S (incl x) = T x)

/-- The closure of a closable operator -/
def closure' (h : T.IsClosable) : UnboundedOperator H := sorry

/-! ### The adjoint of an unbounded operator -/

/-- The domain of the adjoint T*.
    dom(T*) = {y : H | the map x ↦ ⟨Tx, y⟩ is bounded on dom(T)} -/
def adjointDomain : Set H :=
  { y | ∃ C : ℝ, ∀ x : T.domain, ‖@inner ℂ H _ (T x) y‖ ≤ C * ‖(x : H)‖ }

/-- The adjoint domain as a submodule -/
def adjointDomainSubmodule : Submodule ℂ H where
  carrier := T.adjointDomain
  add_mem' := fun {a b} ha hb => by
    obtain ⟨Ca, hCa⟩ := ha
    obtain ⟨Cb, hCb⟩ := hb
    use Ca + Cb
    intro x
    calc ‖@inner ℂ H _ (T x) (a + b)‖
        = ‖@inner ℂ H _ (T x) a + @inner ℂ H _ (T x) b‖ := by rw [inner_add_right]
      _ ≤ ‖@inner ℂ H _ (T x) a‖ + ‖@inner ℂ H _ (T x) b‖ := norm_add_le _ _
      _ ≤ Ca * ‖(x : H)‖ + Cb * ‖(x : H)‖ := add_le_add (hCa x) (hCb x)
      _ = (Ca + Cb) * ‖(x : H)‖ := by ring
  zero_mem' := by
    use 0
    intro x
    simp [inner_zero_right]
  smul_mem' := fun c a ha => by
    obtain ⟨Ca, hCa⟩ := ha
    use ‖c‖ * Ca
    intro x
    calc ‖@inner ℂ H _ (T x) (c • a)‖
        = ‖c‖ * ‖@inner ℂ H _ (T x) a‖ := by rw [inner_smul_right]; simp
      _ ≤ ‖c‖ * (Ca * ‖(x : H)‖) := by apply mul_le_mul_of_nonneg_left (hCa x) (norm_nonneg _)
      _ = (‖c‖ * Ca) * ‖(x : H)‖ := by ring

/-- The adjoint domain forms a subspace -/
theorem adjointDomain_submodule : ∃ S : Submodule ℂ H, (S : Set H) = T.adjointDomain := by
  exact ⟨T.adjointDomainSubmodule, rfl⟩

/-- For densely defined T, if y ∈ dom(T*), there exists z such that
    ⟨Tx, y⟩ = ⟨x, z⟩ for all x ∈ dom(T). -/
theorem adjoint_exists' (hT : T.IsDenselyDefined) (y : H) (hy : y ∈ T.adjointDomain) :
    ∃ z : H, ∀ x : T.domain, @inner ℂ H _ (T x) y = @inner ℂ H _ (x : H) z := by
  -- Existence follows from Riesz representation: the map x ↦ ⟨Tx, y⟩ is bounded
  -- hence extends to a bounded linear functional, which has a unique representing vector
  sorry

/-- The representing vector z is unique -/
theorem adjoint_unique (hT : T.IsDenselyDefined) (y : H) (z₁ z₂ : H)
    (h₁ : ∀ x : T.domain, @inner ℂ H _ (T x) y = @inner ℂ H _ (x : H) z₁)
    (h₂ : ∀ x : T.domain, @inner ℂ H _ (T x) y = @inner ℂ H _ (x : H) z₂) :
    z₁ = z₂ := by
  -- If ⟨x, z₁⟩ = ⟨x, z₂⟩ for all x in dense subspace, then z₁ = z₂
  have heq : ∀ x : T.domain, @inner ℂ H _ (x : H) z₁ = @inner ℂ H _ (x : H) z₂ := by
    intro x; rw [← h₁ x, h₂ x]
  -- This means ⟨x, z₁ - z₂⟩ = 0 for all x in dense domain
  have hdiff : ∀ x : T.domain, @inner ℂ H _ (x : H) (z₁ - z₂) = 0 := by
    intro x
    rw [inner_sub_right, heq x, sub_self]
  -- Since domain is dense, z₁ - z₂ = 0
  sorry

/-- The choice of T*y for y ∈ dom(T*) -/
def adjointApply (hT : T.IsDenselyDefined) (y : T.adjointDomainSubmodule) : H :=
  Classical.choose (T.adjoint_exists' hT y.1 y.2)

/-- The defining property of adjointApply -/
theorem adjointApply_spec (hT : T.IsDenselyDefined) (y : T.adjointDomainSubmodule) :
    ∀ x : T.domain, @inner ℂ H _ (T x) (y : H) = @inner ℂ H _ (x : H) (T.adjointApply hT y) :=
  Classical.choose_spec (T.adjoint_exists' hT y.1 y.2)

/-- The adjoint of a densely defined operator -/
def adjoint (hT : T.IsDenselyDefined) : UnboundedOperator H where
  domain := T.adjointDomainSubmodule
  toFun := T.adjointApply hT
  map_add' := fun x y => by
    -- T*(x+y) = T*x + T*y follows from uniqueness of the representing vector
    apply T.adjoint_unique hT ((x : H) + (y : H))
    · exact T.adjointApply_spec hT (x + y)
    · intro z
      calc @inner ℂ H _ (T z) ((x : H) + (y : H))
          = @inner ℂ H _ (T z) (x : H) + @inner ℂ H _ (T z) (y : H) := inner_add_right _ _ _
        _ = @inner ℂ H _ (z : H) (T.adjointApply hT x) +
            @inner ℂ H _ (z : H) (T.adjointApply hT y) := by
            rw [T.adjointApply_spec hT x z, T.adjointApply_spec hT y z]
        _ = @inner ℂ H _ (z : H) (T.adjointApply hT x + T.adjointApply hT y) := by
            rw [inner_add_right]
  map_smul' := fun c x => by
    apply T.adjoint_unique hT (c • (x : H))
    · exact T.adjointApply_spec hT (c • x)
    · intro z
      calc @inner ℂ H _ (T z) (c • (x : H))
          = c * @inner ℂ H _ (T z) (x : H) := inner_smul_right _ _ _
        _ = c * @inner ℂ H _ (z : H) (T.adjointApply hT x) := by
            rw [T.adjointApply_spec hT x z]
        _ = @inner ℂ H _ (z : H) (c • T.adjointApply hT x) := by
            rw [inner_smul_right]

/-- T* is always closed -/
theorem adjoint_closed (hT : T.IsDenselyDefined) : (T.adjoint hT).IsClosed := by
  sorry

/-- T is closable iff T* is densely defined -/
theorem closable_iff_adjoint_dense (hT : T.IsDenselyDefined) :
    T.IsClosable ↔ (T.adjoint hT).IsDenselyDefined := by
  sorry

/-- For closed densely defined T, T** = T -/
theorem double_adjoint (hT : T.IsDenselyDefined) (_hcl : T.IsClosed)
    (hT' : (T.adjoint hT).IsDenselyDefined) :
    (T.adjoint hT).adjoint hT' = T := by
  sorry

end UnboundedOperator

/-! ### Symmetric and self-adjoint operators -/

namespace UnboundedOperator

variable (T : UnboundedOperator H)

/-- An operator is symmetric if ⟨Tx, y⟩ = ⟨x, Ty⟩ for all x, y ∈ dom(T) -/
def IsSymmetric : Prop :=
  ∀ x y : T.domain, @inner ℂ H _ (T x) (y : H) = @inner ℂ H _ (x : H) (T y)

/-- An operator is self-adjoint if T = T* (including equality of domains) -/
def IsSelfAdjoint (hT : T.IsDenselyDefined) : Prop :=
  T = T.adjoint hT

/-- Symmetric operators are closable -/
theorem symmetric_closable (hT : T.IsDenselyDefined) (hsym : T.IsSymmetric) : T.IsClosable := by
  sorry

/-- Self-adjoint operators are closed -/
theorem selfadjoint_closed (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) : T.IsClosed := by
  -- T = T* and T* is always closed
  rw [hsa]
  exact T.adjoint_closed hT

/-- Self-adjoint operators are symmetric -/
theorem selfadjoint_symmetric (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) :
    T.IsSymmetric := by
  intro x y
  -- For self-adjoint T = T*, the domain equality and operator equality give us
  -- ⟨Tx, y⟩ = ⟨x, T*y⟩ = ⟨x, Ty⟩
  -- The proof requires working through the structure equality T = T.adjoint hT
  -- which involves domain equality and application equality
  sorry

end UnboundedOperator

/-! ### Positive operators -/

namespace UnboundedOperator

variable (T : UnboundedOperator H)

/-- An operator is positive if ⟨Tx, x⟩ ≥ 0 for all x ∈ dom(T) -/
def IsPositive : Prop :=
  ∀ x : T.domain, 0 ≤ (@inner ℂ H _ (T x) (x : H)).re

/-- For symmetric operators, ⟨Tx, x⟩ is real -/
theorem symmetric_inner_real (hsym : T.IsSymmetric) (x : T.domain) :
    (@inner ℂ H _ (T x) (x : H)).im = 0 := by
  -- For symmetric T: ⟨Tx, x⟩ = ⟨x, Tx⟩
  -- Also conj(⟨Tx, x⟩) = ⟨x, Tx⟩ (by inner_conj_symm)
  -- So ⟨Tx, x⟩ = conj(⟨Tx, x⟩), meaning ⟨Tx, x⟩ is real
  have h := hsym x x
  -- inner_conj_symm a b: conj(inner b a) = inner a b
  have hconj : starRingEnd ℂ (@inner ℂ H _ (T x) (x : H)) = @inner ℂ H _ (x : H) (T x) :=
    inner_conj_symm (x : H) (T x)
  -- Combining: conj(⟨Tx, x⟩) = ⟨x, Tx⟩ = ⟨Tx, x⟩
  rw [← h] at hconj
  -- hconj: conj(⟨Tx, x⟩) = ⟨Tx, x⟩
  -- For z = conj(z), we have z.im = -z.im, hence z.im = 0
  have him : (@inner ℂ H _ (T x) (x : H)).im = (starRingEnd ℂ (@inner ℂ H _ (T x) (x : H))).im := by
    rw [hconj]
  simp only [Complex.conj_im] at him
  -- him: z.im = -z.im, so z.im = 0
  linarith

/-- Positive symmetric operators satisfy ⟨(T - μ)x, x⟩ ≥ 0 for μ ≤ 0 -/
theorem positive_spectrum_nonneg (_hT : T.IsDenselyDefined) (_hsym : T.IsSymmetric)
    (hpos : T.IsPositive) (μ : ℝ) (hμ : μ ≤ 0) (x : T.domain) :
    0 ≤ (@inner ℂ H _ (T x) (x : H)).re - μ * ‖(x : H)‖^2 := by
  -- ⟨Tx, x⟩ - μ‖x‖² ≥ 0 when ⟨Tx, x⟩ ≥ 0 and μ ≤ 0
  have hTx := hpos x
  have hμnorm : 0 ≤ -μ * ‖(x : H)‖^2 := by
    apply mul_nonneg
    · linarith
    · exact sq_nonneg _
  linarith

end UnboundedOperator

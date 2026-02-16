import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic

namespace ModularPhysics.Core.QFT.BV.LInfinity

/-!
# L∞ Algebras (Strongly Homotopy Lie Algebras)

L∞ algebras are a generalization of Lie algebras where the Jacobi identity holds
only up to coherent higher homotopies. They arise naturally in:

- Classical BV formalism: The antibracket forms the l₂ bracket
- String field theory: Open/closed string interactions
- Deformation theory: L∞ algebras control deformations
- Derived geometry: Tangent complexes carry L∞ structure

## Mathematical structure:

An L∞ algebra is a ℤ-graded vector space V with multilinear maps
  l_n : V^⊗n → V  for n ≥ 1
of degree 2-n, satisfying the generalized Jacobi identities.

## Connection to Classical BV:

The classical master equation (S,S) = 0 is the Maurer-Cartan equation
for an L∞ algebra with l₂ = antibracket.

Note: The quantum master equation involves additional structure (the BV Laplacian Δ)
that is not part of the L∞ algebra framework. See BatalinVilkovisky.lean for quantum BV.
-/

/- ============= GRADED VECTOR SPACES ============= -/

/-- A ℤ-graded vector space over ℝ

    V = ⊕_{n ∈ ℤ} V_n where V_n is the degree-n component -/
structure GradedVectorSpace where
  /-- The underlying type (total space) -/
  carrier : Type
  /-- Degree function assigning an integer to each element -/
  degree : carrier → ℤ
  /-- Zero element -/
  zero : carrier
  /-- Zero has degree 0 (by convention) -/
  zero_degree : degree zero = 0
  /-- Addition -/
  add : carrier → carrier → carrier
  /-- Scalar multiplication -/
  smul : ℝ → carrier → carrier
  /-- Negation -/
  neg : carrier → carrier
  /-- smul 0 = zero -/
  smul_zero : ∀ v, smul 0 v = zero

/-- Homogeneous element of degree n -/
def GradedVectorSpace.Homogeneous (V : GradedVectorSpace) (v : V.carrier) (n : ℤ) : Prop :=
  V.degree v = n

/- ============= KOSZUL SIGNS ============= -/

/-- Koszul sign for transposing elements of degrees p and q

    When transposing homogeneous elements a, b of degrees |a|, |b|,
    we pick up a sign (-1)^{|a||b|}. -/
def koszulSign (p q : ℤ) : ℤ :=
  if p % 2 = 0 ∨ q % 2 = 0 then 1 else -1

/-- Koszul sign is symmetric -/
theorem koszulSign_comm (p q : ℤ) : koszulSign p q = koszulSign q p := by
  unfold koszulSign
  simp only [or_comm]

/-- Koszul sign for odd elements is -1 -/
theorem koszulSign_odd_odd : koszulSign 1 1 = -1 := by
  unfold koszulSign
  simp

/- ============= L∞ ALGEBRA DEFINITION ============= -/

/-- L∞ algebra (strongly homotopy Lie algebra)

    A graded vector space V equipped with multilinear brackets l_n : V^⊗n → V
    satisfying the generalized Jacobi identities.

    We define l_n for n = 1, 2, 3 explicitly; higher brackets can be added. -/
structure LInfinityAlgebra where
  /-- The underlying graded vector space -/
  V : GradedVectorSpace
  /-- l₁ : V → V is a differential of degree 1 -/
  l1 : V.carrier → V.carrier
  /-- l₁ has degree 1 -/
  l1_degree : ∀ v, V.degree (l1 v) = V.degree v + 1
  /-- l₂ : V ⊗ V → V is the bracket of degree 0 -/
  l2 : V.carrier → V.carrier → V.carrier
  /-- l₂ has degree 0 (sum of input degrees) -/
  l2_degree : ∀ v w, V.degree (l2 v w) = V.degree v + V.degree w
  /-- l₃ : V^⊗3 → V is the Jacobiator of degree -1 -/
  l3 : V.carrier → V.carrier → V.carrier → V.carrier
  /-- l₃ has degree -1 -/
  l3_degree : ∀ u v w, V.degree (l3 u v w) = V.degree u + V.degree v + V.degree w - 1

/- ============= L∞ RELATIONS ============= -/

/-- l₁ is a differential: l₁ ∘ l₁ = 0

    This is the n=1 generalized Jacobi identity. -/
def l1_squared_zero (L : LInfinityAlgebra) : Prop :=
  ∀ v, L.l1 (L.l1 v) = L.V.zero

/-- l₂ graded antisymmetry: l₂(v,w) = -(-1)^{|v||w|} l₂(w,v) -/
def l2_graded_antisymmetric (L : LInfinityAlgebra) : Prop :=
  ∀ v w, L.l2 v w = L.V.smul (koszulSign (L.V.degree v) (L.V.degree w) * (-1)) (L.l2 w v)

/-- l₁ is a derivation of l₂ (up to l₃ correction)

    l₁(l₂(v,w)) = l₂(l₁v, w) + (-1)^|v| l₂(v, l₁w)

    This is part of the n=2 generalized Jacobi identity for a DGLA.
    For a general L∞, there's an l₃ correction term. -/
def l1_derivation (L : LInfinityAlgebra) : Prop :=
  ∀ v w, L.l1 (L.l2 v w) = L.V.add (L.l2 (L.l1 v) w)
    (L.V.smul (if L.V.degree v % 2 = 0 then 1 else -1) (L.l2 v (L.l1 w)))

/-- Jacobi identity for l₂ up to homotopy

    For a Lie algebra: l₂(l₂(u,v),w) + cyclic = 0
    For an L∞ algebra: l₂(l₂(u,v),w) + cyclic = l₁(l₃(u,v,w)) + boundary terms

    The l₃ bracket measures the failure of strict Jacobi. -/
def jacobi_up_to_homotopy (L : LInfinityAlgebra) : Prop :=
  ∀ u v w,
    L.V.add (L.V.add (L.l2 (L.l2 u v) w) (L.l2 (L.l2 v w) u)) (L.l2 (L.l2 w u) v) =
    L.l1 (L.l3 u v w)  -- Plus other terms involving l₃

/- ============= SPECIAL CASES ============= -/

/-- Differential graded Lie algebra (DGLA)

    An L∞ algebra where l_n = 0 for all n ≥ 3.
    The Jacobi identity holds strictly. -/
structure DGLA extends LInfinityAlgebra where
  /-- l₃ vanishes -/
  l3_zero : ∀ u v w, l3 u v w = V.zero
  /-- l₁² = 0 -/
  differential : l1_squared_zero toLInfinityAlgebra
  /-- l₁ is a derivation -/
  derivation : l1_derivation toLInfinityAlgebra
  /-- Strict Jacobi identity -/
  jacobi : ∀ u v w,
    V.add (V.add (l2 (l2 u v) w) (l2 (l2 v w) u)) (l2 (l2 w u) v) = V.zero

/-- Lie algebra as L∞ algebra with l₁ = 0 and l_n = 0 for n ≥ 3 -/
structure LieAsLInfinity extends LInfinityAlgebra where
  /-- l₁ = 0 -/
  l1_zero : ∀ v, l1 v = V.zero
  /-- l₃ = 0 -/
  l3_zero : ∀ u v w, l3 u v w = V.zero
  /-- Antisymmetry of bracket -/
  antisymmetric : l2_graded_antisymmetric toLInfinityAlgebra
  /-- Jacobi identity -/
  jacobi : ∀ u v w,
    V.add (V.add (l2 (l2 u v) w) (l2 (l2 v w) u)) (l2 (l2 w u) v) = V.zero

/- ============= MAURER-CARTAN EQUATION ============= -/

/-- Maurer-Cartan element

    An element a ∈ V of degree 1 satisfying:
    l₁(a) + (1/2)l₂(a,a) + (1/6)l₃(a,a,a) + ... = 0

    For DGLA: l₁(a) + (1/2)l₂(a,a) = 0
    For Lie algebra: (1/2)[a,a] = 0 (automatic for degree reasons) -/
structure MaurerCartanElement (L : LInfinityAlgebra) where
  /-- The element -/
  element : L.V.carrier
  /-- Has degree 1 -/
  degree_one : L.V.degree element = 1
  /-- Satisfies MC equation (truncated at l₃) -/
  mc_equation : L.V.add (L.V.add (L.l1 element)
    (L.V.smul (1/2) (L.l2 element element)))
    (L.V.smul (1/6) (L.l3 element element element)) = L.V.zero

/-- Maurer-Cartan equation for DGLA (simpler form) -/
def MaurerCartanDGLA (D : DGLA) (a : D.V.carrier) : Prop :=
  D.V.add (D.l1 a) (D.V.smul (1/2) (D.l2 a a)) = D.V.zero

/- ============= CLASSICAL BV AS L∞ ============= -/

/-- Classical BV structure as an L∞ algebra

    The classical BV formalism (without Δ) is an L∞ algebra where:
    - l₁ = 0 (no differential at classical level)
    - l₂ = antibracket (,)
    - l₃, l₄, ... encode open gauge algebras

    The classical master equation (S,S) = 0 is exactly l₂(S,S) = 0,
    which is the Maurer-Cartan equation when l₁ = 0.

    IMPORTANT: This does NOT include the quantum BV Laplacian Δ.
    The quantum master equation requires additional structure. -/
structure ClassicalBVAsLInfinity extends LInfinityAlgebra where
  /-- l₁ = 0 at classical level -/
  l1_zero : ∀ v, l1 v = V.zero
  /-- Antibracket is graded antisymmetric -/
  antisymmetric : l2_graded_antisymmetric toLInfinityAlgebra

/-- Classical master equation is Maurer-Cartan equation

    When l₁ = 0, the MC equation reduces to l₂(S,S) = 0,
    which is exactly (S,S) = 0 since l₂ = antibracket. -/
def classicalMasterIsMC (bv : ClassicalBVAsLInfinity) (S : bv.V.carrier) : Prop :=
  bv.l2 S S = bv.V.zero

/- ============= HOMOTOPY TRANSFER ============= -/

/-- Homotopy transfer data

    Given chain complexes (V, d_V) and (H, d_H) with maps
    p : V → H (projection), i : H → V (inclusion), h : V → V (homotopy)
    satisfying p ∘ i = id and i ∘ p - id = d_V ∘ h + h ∘ d_V,
    an L∞ structure on V transfers to H. -/
structure HomotopyTransferData (V H : GradedVectorSpace) where
  /-- Projection p : V → H -/
  projection : V.carrier → H.carrier
  /-- Inclusion i : H → V -/
  inclusion : H.carrier → V.carrier
  /-- Homotopy h : V → V of degree -1 -/
  homotopy : V.carrier → V.carrier
  /-- h has degree -1 -/
  homotopy_degree : ∀ v, V.degree (homotopy v) = V.degree v - 1
  /-- p ∘ i = id -/
  proj_incl : ∀ x, projection (inclusion x) = x

/-- L∞ algebra structure on a specific graded vector space -/
structure LInfinityOn (V : GradedVectorSpace) where
  /-- l₁ : V → V is a differential of degree 1 -/
  l1 : V.carrier → V.carrier
  /-- l₁ has degree 1 -/
  l1_degree : ∀ v, V.degree (l1 v) = V.degree v + 1
  /-- l₂ : V ⊗ V → V is the bracket of degree 0 -/
  l2 : V.carrier → V.carrier → V.carrier
  /-- l₂ has degree 0 -/
  l2_degree : ∀ v w, V.degree (l2 v w) = V.degree v + V.degree w
  /-- l₃ : V^⊗3 → V is the Jacobiator of degree -1 -/
  l3 : V.carrier → V.carrier → V.carrier → V.carrier
  /-- l₃ has degree -1 -/
  l3_degree : ∀ u v w, V.degree (l3 u v w) = V.degree u + V.degree v + V.degree w - 1

/-- Convert LInfinityOn to LInfinityAlgebra -/
def LInfinityOn.toLInfinityAlgebra {V : GradedVectorSpace} (L : LInfinityOn V) :
    LInfinityAlgebra where
  V := V
  l1 := L.l1
  l1_degree := L.l1_degree
  l2 := L.l2
  l2_degree := L.l2_degree
  l3 := L.l3
  l3_degree := L.l3_degree

/-- The transferred l₁ bracket under homotopy transfer

    Given an L∞ structure on V and homotopy transfer data to H,
    the transferred l₁ is: l₁^H = p ∘ l₁^V ∘ i -/
def transferredL1 {V H : GradedVectorSpace} (data : HomotopyTransferData V H)
    (L : LInfinityOn V) : H.carrier → H.carrier :=
  fun x => data.projection (L.l1 (data.inclusion x))

/-- The transferred l₂ bracket under homotopy transfer

    l₂^H(x,y) = p ∘ l₂^V(i(x), i(y)) + higher corrections involving homotopy h -/
def transferredL2 {V H : GradedVectorSpace} (data : HomotopyTransferData V H)
    (L : LInfinityOn V) : H.carrier → H.carrier → H.carrier :=
  fun x y => data.projection (L.l2 (data.inclusion x) (data.inclusion y))

end ModularPhysics.Core.QFT.BV.LInfinity

import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.TQFT

set_option linter.unusedVariables false

/- ============= MANIFOLDS AND BORDISMS ============= -/

/-- n-dimensional smooth manifold -/
axiom Manifold (n : ℕ) : Type

/-- Manifold with boundary -/
axiom ManifoldWithBoundary (n : ℕ) : Type

/-- Coercion from manifold with boundary to manifold -/
noncomputable axiom ManifoldWithBoundary.toManifold (n : ℕ) : ManifoldWithBoundary n → Manifold n

noncomputable instance (n : ℕ) : Coe (ManifoldWithBoundary n) (Manifold n) where
  coe := ManifoldWithBoundary.toManifold n

/-- Boundary of a manifold -/
axiom boundary {n : ℕ} : ManifoldWithBoundary n → Manifold (n-1)

/-- Empty manifold -/
axiom emptyManifold (n : ℕ) : Manifold n

/-- Homeomorphic relation -/
axiom Homeomorphic {n : ℕ} : ManifoldWithBoundary n → ManifoldWithBoundary n → Prop

/-- Closed manifold (no boundary) -/
def ClosedManifold (n : ℕ) := {M : ManifoldWithBoundary n // boundary M = emptyManifold (n-1)}

/-- n-sphere S^n -/
axiom sphere (n : ℕ) : Manifold n

/-- n-torus T^n -/
axiom torus (n : ℕ) : Manifold n

/-- Bordism: cobordism between (n-1)-manifolds -/
axiom Bordism (n : ℕ) : Type

/-- Source and target of bordism -/
axiom bordismBoundary {n : ℕ} : Bordism n → Manifold (n-1) × Manifold (n-1)

/-- Source of bordism -/
noncomputable def bordismSource {n : ℕ} (W : Bordism n) : Manifold (n-1) :=
  (bordismBoundary W).1

/-- Target of bordism -/
noncomputable def bordismTarget {n : ℕ} (W : Bordism n) : Manifold (n-1) :=
  (bordismBoundary W).2

/-- Bordism composition (gluing along boundary) -/
axiom bordismCompose {n : ℕ} (W₁ W₂ : Bordism n) : Bordism n

/-- Disjoint union of manifolds -/
axiom disjointUnionManifold {n : ℕ} : Manifold n → Manifold n → Manifold n

/-- Disjoint union of bordisms -/
axiom disjointUnion {n : ℕ} : Bordism n → Bordism n → Bordism n

/-- Identity bordism (cylinder) -/
axiom identityBordism {n : ℕ} (M : Manifold (n-1)) : Bordism n

/-- Bordism category -/
axiom BordismCategory (n : ℕ) : Type

/-- Identity bordism properties -/
axiom identity_bordism_props {n : ℕ} (M : Manifold (n-1)) :
  bordismBoundary (identityBordism M) = (M, M)

/-- Functoriality: Z(W₂ ∘ W₁) = Z(W₂) ∘ Z(W₁) -/
axiom functoriality {n : ℕ} (W₁ W₂ : Bordism n) :
  bordismTarget W₁ = bordismSource W₂ →
  bordismBoundary (bordismCompose W₁ W₂) = (bordismSource W₁, bordismTarget W₂)

/- ============= STRUCTURE ON MANIFOLDS ============= -/

/-- Oriented manifold -/
axiom OrientedManifold (n : ℕ) : Type

/-- Framed manifold (trivialized tangent bundle) -/
axiom FramedManifold (n : ℕ) : Type

/-- Spin manifold -/
axiom SpinManifold (n : ℕ) : Type

/-- Manifold with G-structure -/
axiom GStructureManifold (G : Type) (n : ℕ) : Type

/-- Orientation reversal -/
axiom reverseOrientation {n : ℕ} : OrientedManifold n → OrientedManifold n

/-- Embed oriented manifold as manifold -/
axiom orientedToManifold {n : ℕ} : OrientedManifold n → Manifold n

/-- Framing determines orientation -/
axiom framing_gives_orientation {n : ℕ} :
  FramedManifold n → OrientedManifold n

/-- Surface of genus g -/
axiom surfaceGenus (g : ℕ) : Manifold 2

/-- Triangulation of manifold -/
axiom Triangulation (M : Manifold n) : Type

/-- Bordism n-category -/
axiom bordismNCategory (n : ℕ) : Type

/-- Bicategory -/
axiom Bicategory : Type

/-- Bordism 2-category -/
axiom bordism2Category : Bicategory

end ModularPhysics.Core.QFT.TQFT

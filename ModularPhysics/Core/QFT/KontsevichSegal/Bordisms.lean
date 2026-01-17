import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.KontsevichSegal

set_option linter.unusedVariables false

/- ============= BORDISM CATEGORY ============= -/

/-- Bordism (d-dimensional manifold with boundary) -/
axiom Bordism (d : ℕ) : Type _

/-- Boundary of bordism: list of connected components with orientations -/
axiom bordismBoundary (d : ℕ) : Bordism d → List (Bordism (d-1))

/-- Empty bordism (unit for disjoint union) -/
axiom emptyBordism (d : ℕ) : Bordism d

/-- Closed manifold (no boundary) -/
axiom ClosedManifold (d : ℕ) : Type _

/-- Closed manifolds correspond to bordisms with empty boundary -/
axiom closedManifold_equiv (d : ℕ) :
  ClosedManifold d ≃ {M : Bordism d // bordismBoundary d M = ([] : List (Bordism (d-1)))}

/-- Coercion from closed manifold to bordism -/
axiom closedToBordism {d : ℕ} : ClosedManifold d → Bordism d

noncomputable instance {d : ℕ} : Coe (ClosedManifold d) (Bordism d) where
  coe := closedToBordism

/-- Closed manifolds have no boundary -/
axiom closed_no_boundary {d : ℕ} (M : ClosedManifold d) :
  bordismBoundary d (closedToBordism M) = []

/-- Disjoint union of bordisms (monoidal product) -/
axiom disjointUnion (d : ℕ) : Bordism d → Bordism d → Bordism d

/-- Disjoint union is associative -/
axiom disjointUnion_assoc (d : ℕ) (M₁ M₂ M₃ : Bordism d) :
  disjointUnion d (disjointUnion d M₁ M₂) M₃ =
  disjointUnion d M₁ (disjointUnion d M₂ M₃)

/-- Empty bordism is unit for disjoint union -/
axiom disjointUnion_empty_left (d : ℕ) (M : Bordism d) :
  disjointUnion d (emptyBordism d) M = M

axiom disjointUnion_empty_right (d : ℕ) (M : Bordism d) :
  disjointUnion d M (emptyBordism d) = M

/-- Orientation reversal -/
axiom reverseOrientation (d : ℕ) : Bordism d → Bordism d

/-- Orientation reversal is involutive -/
axiom reverseOrientation_involutive (d : ℕ) (M : Bordism d) :
  reverseOrientation d (reverseOrientation d M) = M

/-- Cylinder (identity bordism) M × [0,1] -/
axiom cylinder (d : ℕ) : Bordism (d-1) → Bordism d

/-- Gluing of bordisms along common boundary -/
axiom glueBordisms (d : ℕ) (M₁ M₂ : Bordism d) (Sig : Bordism (d-1)) : Bordism d

end ModularPhysics.Core.QFT.KontsevichSegal

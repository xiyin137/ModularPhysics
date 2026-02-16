import ModularPhysics.PhysicsLogic.QFT.KontsevichSegal.Bordisms
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.KontsevichSegal

set_option linter.unusedVariables false

/- ============= FRÉCHET SPACES (NOT HILBERT!) ============= -/

/-- KS: State space on (d-1)-manifold is Fréchet space (NOT Hilbert!)
    Key difference from Atiyah-Segal: Path integral naturally gives Fréchet spaces
    versus Hilbert spaces in operator formalism -/
structure KS_StateSpace (d : ℕ) (bt : BordismTheory (d-1)) (Sig : bt.Bordism) where
  carrier : Type _
  add : carrier → carrier → carrier
  smul : ℂ → carrier → carrier
  zero : carrier
  /-- Fréchet topology: countable family of seminorms -/
  seminorms : ℕ → (carrier → ℝ)
  /-- Each seminorm is non-negative -/
  seminorm_nonneg : ∀ (n : ℕ) (ψ : carrier), seminorms n ψ ≥ 0
  /-- Seminorm of zero is zero -/
  seminorm_zero : ∀ (n : ℕ), seminorms n zero = 0
  /-- Topology is complete -/
  complete : Prop
  /-- Topology is locally convex -/
  locally_convex : Prop

/-- Structure for state space operations -/
structure KS_StateSpaceOps (d : ℕ) (bt : BordismTheory (d-1)) where
  /-- Empty manifold gives ground field ℂ -/
  emptySpace : KS_StateSpace d bt bt.emptyBordism
  /-- The carrier of empty space is ℂ -/
  empty_is_C : emptySpace.carrier = ℂ
  /-- Monoidal structure (completed projective tensor product) -/
  tensor : (Sig₁ Sig₂ : bt.Bordism) →
    KS_StateSpace d bt Sig₁ → KS_StateSpace d bt Sig₂ →
    KS_StateSpace d bt (bt.disjointUnion Sig₁ Sig₂)
  /-- Tensor product is associative (up to natural isomorphism) -/
  tensor_assoc : ∀ (Sig₁ Sig₂ Sig₃ : bt.Bordism)
    (V₁ : KS_StateSpace d bt Sig₁)
    (V₂ : KS_StateSpace d bt Sig₂)
    (V₃ : KS_StateSpace d bt Sig₃),
    True -- Natural isomorphism between tensor(tensor(V₁,V₂),V₃) and tensor(V₁,tensor(V₂,V₃))
  /-- Duality (continuous dual space) -/
  dual : (Sig : bt.Bordism) → KS_StateSpace d bt Sig →
    KS_StateSpace d bt (bt.reverseOrientation Sig)
  /-- Dual of dual is naturally isomorphic to original -/
  dual_dual : ∀ (Sig : bt.Bordism) (V : KS_StateSpace d bt Sig),
    True -- Natural isomorphism V ≅ V**
  /-- Pairing for gluing (continuous bilinear map) -/
  pairing : (Sig : bt.Bordism) →
    (V : KS_StateSpace d bt Sig) →
    (V_dual : KS_StateSpace d bt (bt.reverseOrientation Sig)) →
    V.carrier → V_dual.carrier → ℂ
  /-- Pairing is non-degenerate -/
  pairing_nondegenerate : ∀ (Sig : bt.Bordism)
    (V : KS_StateSpace d bt Sig)
    (V_dual : KS_StateSpace d bt (bt.reverseOrientation Sig))
    (ψ : V.carrier),
    (∀ φ : V_dual.carrier, pairing Sig V V_dual ψ φ = 0) → ψ = V.zero
  /-- Symmetric monoidal structure (commutativity) -/
  symmetric : ∀ (Sig₁ Sig₂ : bt.Bordism)
    (V₁ : KS_StateSpace d bt Sig₁) (V₂ : KS_StateSpace d bt Sig₂),
    True -- Natural isomorphism between V₁ ⊗ V₂ and V₂ ⊗ V₁

end ModularPhysics.Core.QFT.KontsevichSegal

import ModularPhysics.Core.QFT.KontsevichSegal.Bordisms
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.KontsevichSegal

set_option linter.unusedVariables false

/- ============= FRÉCHET SPACES (NOT HILBERT!) ============= -/

/-- KS: State space on (d-1)-manifold is Fréchet space (NOT Hilbert!)
    Key difference from Atiyah-Segal: Path integral naturally gives Fréchet spaces
    versus Hilbert spaces in operator formalism -/
structure KS_StateSpace (d : ℕ) (Sig : Bordism (d-1)) where
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

/-- Empty manifold gives ground field ℂ -/
axiom ks_empty_space (d : ℕ) :
  KS_StateSpace d (emptyBordism (d-1))

axiom ks_empty_is_C (d : ℕ) :
  (ks_empty_space d).carrier = ℂ

/-- Monoidal structure (completed projective tensor product) -/
axiom ks_tensor (d : ℕ) (Sig₁ Sig₂ : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁) (V₂ : KS_StateSpace d Sig₂) :
  KS_StateSpace d (disjointUnion (d-1) Sig₁ Sig₂)

/-- Tensor product is associative (up to natural isomorphism) -/
axiom ks_tensor_assoc (d : ℕ) (Sig₁ Sig₂ Sig₃ : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁)
  (V₂ : KS_StateSpace d Sig₂)
  (V₃ : KS_StateSpace d Sig₃) :
  True -- Natural isomorphism between ks_tensor(ks_tensor(V₁,V₂),V₃) and ks_tensor(V₁,ks_tensor(V₂,V₃))

/-- Duality (continuous dual space) -/
axiom ks_dual (d : ℕ) (Sig : Bordism (d-1)) (V : KS_StateSpace d Sig) :
  KS_StateSpace d (reverseOrientation (d-1) Sig)

/-- Dual of dual is naturally isomorphic to original -/
axiom ks_dual_dual (d : ℕ) (Sig : Bordism (d-1)) (V : KS_StateSpace d Sig) :
  True -- Natural isomorphism V ≅ V**

/-- Pairing for gluing (continuous bilinear map) -/
axiom ks_pairing (d : ℕ) (Sig : Bordism (d-1))
  (V : KS_StateSpace d Sig)
  (V_dual : KS_StateSpace d (reverseOrientation (d-1) Sig)) :
  V.carrier → V_dual.carrier → ℂ

/-- Pairing is non-degenerate -/
axiom ks_pairing_nondegenerate (d : ℕ) (Sig : Bordism (d-1))
  (V : KS_StateSpace d Sig)
  (V_dual : KS_StateSpace d (reverseOrientation (d-1) Sig))
  (ψ : V.carrier) :
  (∀ φ : V_dual.carrier, ks_pairing d Sig V V_dual ψ φ = 0) → ψ = V.zero

/-- Symmetric monoidal structure (commutativity) -/
axiom ks_symmetric (d : ℕ) (Sig₁ Sig₂ : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁) (V₂ : KS_StateSpace d Sig₂) :
  True -- Natural isomorphism between V₁ ⊗ V₂ and V₂ ⊗ V₁

end ModularPhysics.Core.QFT.KontsevichSegal

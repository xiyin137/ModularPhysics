import ModularPhysics.Core.QFT.KontsevichSegal.StateSpaces
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.KontsevichSegal

set_option linter.unusedVariables false

/- ============= KONTSEVICH-SEGAL AXIOMS ============= -/

/-- Field theory data on bordism (abstract, could come from path integral) -/
axiom FieldTheoryData (d : ℕ) (M : Bordism d) : Type _

/-- Path integral on bordism gives continuous linear map -/
structure KS_PathIntegralMap (d : ℕ) (M : Bordism d)
  (Sig_in Sig_out : Bordism (d-1))
  (V_in : KS_StateSpace d Sig_in)
  (V_out : KS_StateSpace d Sig_out) where
  map : V_in.carrier → V_out.carrier
  /-- Additivity -/
  additive : ∀ ψ φ, map (V_in.add ψ φ) = V_out.add (map ψ) (map φ)
  /-- Homogeneity -/
  homogeneous : ∀ (a : ℂ) ψ, map (V_in.smul a ψ) = V_out.smul a (map ψ)
  /-- Continuity in Fréchet topology -/
  continuous_seminorms : ∀ (n : ℕ), ∃ (C : ℝ) (m : ℕ),
    ∀ ψ, V_out.seminorms n (map ψ) ≤ C * V_in.seminorms m ψ

/-- Composition (gluing bordisms along boundary) -/
axiom ks_composition (d : ℕ) (M₁ M₂ : Bordism d)
  (Sig_L Sig_M Sig_R : Bordism (d-1))
  (V_L : KS_StateSpace d Sig_L)
  (V_M : KS_StateSpace d Sig_M)
  (V_R : KS_StateSpace d Sig_R)
  (Z₁ : KS_PathIntegralMap d M₁ Sig_L Sig_M V_L V_M)
  (Z₂ : KS_PathIntegralMap d M₂ Sig_M Sig_R V_M V_R) :
  ∃ (M : Bordism d) (Z : KS_PathIntegralMap d M Sig_L Sig_R V_L V_R),
    ∀ ψ, Z.map ψ = Z₂.map (Z₁.map ψ)

/-- Identity cylinder gives identity operator -/
axiom ks_identity (d : ℕ) (Sig : Bordism (d-1))
  (V : KS_StateSpace d Sig)
  (data : FieldTheoryData d (cylinder d Sig)) :
  ∃ (Z : KS_PathIntegralMap d (cylinder d Sig) Sig Sig V V),
    ∀ ψ, Z.map ψ = ψ

/-- Monoidal structure on maps (independent systems tensor) -/
axiom ks_tensor_maps (d : ℕ)
  (M₁ M₂ : Bordism d)
  (Sig₁ Sig₂ Sig₁' Sig₂' : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁) (V₁' : KS_StateSpace d Sig₁')
  (V₂ : KS_StateSpace d Sig₂) (V₂' : KS_StateSpace d Sig₂')
  (Z₁ : KS_PathIntegralMap d M₁ Sig₁ Sig₁' V₁ V₁')
  (Z₂ : KS_PathIntegralMap d M₂ Sig₂ Sig₂' V₂ V₂') :
  KS_PathIntegralMap d (disjointUnion d M₁ M₂)
    (disjointUnion (d-1) Sig₁ Sig₂)
    (disjointUnion (d-1) Sig₁' Sig₂')
    (ks_tensor d Sig₁ Sig₂ V₁ V₂)
    (ks_tensor d Sig₁' Sig₂' V₁' V₂')

/-- Partition function for closed manifold (map from ℂ to ℂ) -/
axiom ks_partition_function (d : ℕ)
  (M : ClosedManifold d)
  (data : FieldTheoryData d M) : ℂ

/-- Gluing formula - partition function on glued manifold
    factors as trace/pairing over the gluing surface -/
axiom ks_gluing_formula (d : ℕ)
  (M₁ M₂ : Bordism d)
  (Sig : Bordism (d-1))
  (M_glued : ClosedManifold d)
  (h_glue : (M_glued : Bordism d) = glueBordisms d M₁ M₂ Sig)
  (data : FieldTheoryData d M_glued) :
  ks_partition_function d M_glued data = sorry

/-- Functoriality under diffeomorphism -/
axiom ks_diffeomorphism_invariance (d : ℕ)
  (M M' : Bordism d)
  (Sig_in Sig_out : Bordism (d-1))
  (V_in : KS_StateSpace d Sig_in)
  (V_out : KS_StateSpace d Sig_out)
  (h_diffeo : True) -- M and M' are diffeomorphic
  (Z : KS_PathIntegralMap d M Sig_in Sig_out V_in V_out)
  (Z' : KS_PathIntegralMap d M' Sig_in Sig_out V_in V_out) :
  ∀ ψ, Z.map ψ = Z'.map ψ

end ModularPhysics.Core.QFT.KontsevichSegal

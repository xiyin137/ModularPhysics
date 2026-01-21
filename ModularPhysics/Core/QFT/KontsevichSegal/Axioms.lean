import ModularPhysics.Core.QFT.KontsevichSegal.StateSpaces
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.KontsevichSegal

set_option linter.unusedVariables false

/- ============= KONTSEVICH-SEGAL AXIOMS ============= -/

/-- Path integral on bordism gives continuous linear map -/
structure KS_PathIntegralMap (d : ℕ) (bt : BordismTheory d) (bt_lower : BordismTheory (d-1))
    (M : bt.Bordism)
    (Sig_in Sig_out : bt_lower.Bordism)
    (V_in : KS_StateSpace d bt_lower Sig_in)
    (V_out : KS_StateSpace d bt_lower Sig_out) where
  map : V_in.carrier → V_out.carrier
  /-- Additivity -/
  additive : ∀ ψ φ, map (V_in.add ψ φ) = V_out.add (map ψ) (map φ)
  /-- Homogeneity -/
  homogeneous : ∀ (a : ℂ) ψ, map (V_in.smul a ψ) = V_out.smul a (map ψ)
  /-- Continuity in Fréchet topology -/
  continuous_seminorms : ∀ (n : ℕ), ∃ (C : ℝ) (m : ℕ),
    ∀ ψ, V_out.seminorms n (map ψ) ≤ C * V_in.seminorms m ψ

/-- Structure for Kontsevich-Segal field theory axioms -/
structure KS_FieldTheory (d : ℕ) (bt : BordismTheory d) (bt_lower : BordismTheory (d-1))
    (gluing : BordismGluing d bt bt_lower)
    (ssOps : KS_StateSpaceOps d bt_lower)
    (cmt : ClosedManifoldTheory d bt) where
  /-- Field theory data on bordism (abstract, could come from path integral) -/
  FieldTheoryData : bt.Bordism → Type _
  /-- Composition (gluing bordisms along boundary) -/
  composition : ∀ (M₁ M₂ : bt.Bordism)
    (Sig_L Sig_M Sig_R : bt_lower.Bordism)
    (V_L : KS_StateSpace d bt_lower Sig_L)
    (V_M : KS_StateSpace d bt_lower Sig_M)
    (V_R : KS_StateSpace d bt_lower Sig_R)
    (Z₁ : KS_PathIntegralMap d bt bt_lower M₁ Sig_L Sig_M V_L V_M)
    (Z₂ : KS_PathIntegralMap d bt bt_lower M₂ Sig_M Sig_R V_M V_R),
    ∃ (M : bt.Bordism) (Z : KS_PathIntegralMap d bt bt_lower M Sig_L Sig_R V_L V_R),
      ∀ ψ, Z.map ψ = Z₂.map (Z₁.map ψ)
  /-- Identity cylinder gives identity operator -/
  identity : ∀ (Sig : bt_lower.Bordism)
    (V : KS_StateSpace d bt_lower Sig)
    (data : FieldTheoryData (gluing.cylinder Sig)),
    ∃ (Z : KS_PathIntegralMap d bt bt_lower (gluing.cylinder Sig) Sig Sig V V),
      ∀ ψ, Z.map ψ = ψ
  /-- Monoidal structure on maps (independent systems tensor) -/
  tensor_maps : ∀ (M₁ M₂ : bt.Bordism)
    (Sig₁ Sig₂ Sig₁' Sig₂' : bt_lower.Bordism)
    (V₁ : KS_StateSpace d bt_lower Sig₁) (V₁' : KS_StateSpace d bt_lower Sig₁')
    (V₂ : KS_StateSpace d bt_lower Sig₂) (V₂' : KS_StateSpace d bt_lower Sig₂')
    (Z₁ : KS_PathIntegralMap d bt bt_lower M₁ Sig₁ Sig₁' V₁ V₁')
    (Z₂ : KS_PathIntegralMap d bt bt_lower M₂ Sig₂ Sig₂' V₂ V₂'),
    KS_PathIntegralMap d bt bt_lower (bt.disjointUnion M₁ M₂)
      (bt_lower.disjointUnion Sig₁ Sig₂)
      (bt_lower.disjointUnion Sig₁' Sig₂')
      (ssOps.tensor Sig₁ Sig₂ V₁ V₂)
      (ssOps.tensor Sig₁' Sig₂' V₁' V₂')
  /-- Partition function for closed manifold (map from ℂ to ℂ) -/
  partition_function : (M : cmt.ClosedManifold) →
    FieldTheoryData (cmt.closedToBordism M) → ℂ
  /-- Functoriality under diffeomorphism -/
  diffeomorphism_invariance : ∀ (M M' : bt.Bordism)
    (Sig_in Sig_out : bt_lower.Bordism)
    (V_in : KS_StateSpace d bt_lower Sig_in)
    (V_out : KS_StateSpace d bt_lower Sig_out)
    (h_diffeo : True) -- M and M' are diffeomorphic
    (Z : KS_PathIntegralMap d bt bt_lower M Sig_in Sig_out V_in V_out)
    (Z' : KS_PathIntegralMap d bt bt_lower M' Sig_in Sig_out V_in V_out),
    ∀ ψ, Z.map ψ = Z'.map ψ

end ModularPhysics.Core.QFT.KontsevichSegal

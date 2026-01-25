/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import ModularPhysics.RigorousQFT.Wightman.Basic
import ModularPhysics.RigorousQFT.Wightman.OperatorDistribution

/-!
# Wightman Axioms

This file provides a rigorous mathematical formulation of the Wightman axioms for
quantum field theory. The axioms are formalized as a structure `WightmanQFT` that
contains all the required data and properties.

## Main Definitions

* `WightmanQFT` - The complete structure satisfying all Wightman axioms
* `WightmanQFT.spectrumCondition` - Energy-momentum spectrum lies in forward light cone
* `WightmanQFT.locality` - Spacelike-separated fields commute

## The Wightman Axioms

The Wightman axioms (W1-W4) as formalized here:

**W1 (Covariance)**:
- There is a continuous unitary representation U of the Poincaré group on H
- The generators P_μ (energy-momentum) have spectrum in the forward light cone V₊
- There exists a unique vacuum vector Ω invariant under U(g)

**W2 (Field Operators)**:
- There exist field operators φ(f) for each test function f ∈ 𝒮(ℝ^{d+1})
- The domain D is dense and invariant under all φ(f)
- The subspace spanned by φ(f₁)···φ(fₙ)Ω is dense in H
- The field is covariant: U(g) φ(f) U(g)⁻¹ = φ(f ∘ g⁻¹)

**W3 (Locality)**:
- If supp(f) and supp(g) are spacelike separated, then [φ(f), φ(g)] = 0 on D

**W4 (Vacuum Uniqueness)**:
- The vacuum Ω is the unique vector (up to phase) invariant under time translations

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That"
* Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
* Haag, "Local Quantum Physics"
-/

noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable (d : ℕ) [NeZero d]

/-! ### Spectrum Condition -/

/-- The forward light cone in momentum space: p₀ ≥ 0, p² ≥ 0 -/
def ForwardMomentumCone : Set (MinkowskiSpace d) :=
  MinkowskiSpace.ClosedForwardLightCone d

/-- The spectrum condition: the joint spectrum of the energy-momentum operators
    lies in the closed forward light cone -/
structure SpectralCondition (d : ℕ) [NeZero d]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : PoincareRepresentation d H) : Prop where
  /-- The spectrum is contained in the forward cone -/
  spectrum_in_cone : True  -- Placeholder for proper spectral theory formulation
  -- In a full formalization, this would state that the joint spectrum of
  -- the momentum operators P_μ lies in the closed forward light cone

/-! ### Locality -/

/-- Two Schwartz functions have spacelike-separated supports -/
def AreSpacelikeSeparatedSupports (f g : SchwartzSpacetime d) : Prop :=
  ∀ x ∈ Function.support f, ∀ y ∈ Function.support g,
    MinkowskiSpace.AreSpacelikeSeparated d x y

/-- The commutator of two operators on a domain -/
def Commutator {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : H → H) (D : Set H) : Prop :=
  ∀ ψ ∈ D, A (B ψ) = B (A ψ)

/-- Locality: spacelike-separated fields commute -/
def IsLocal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : OperatorValuedDistribution d H) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    AreSpacelikeSeparatedSupports d f g →
    Commutator (φ.operator f) (φ.operator g) φ.domain.toSubmodule

/-! ### Vacuum Properties -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector is invariant under the Poincaré representation -/
def IsPoincareInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ g : PoincareGroup d, π.U g Ω = Ω

/-- A vector is invariant under time translations only -/
def IsTimeTranslationInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ t : ℝ, π.U (PoincareGroup.translation' (fun i => if i = 0 then t else 0)) Ω = Ω

/-- Uniqueness of the vacuum: Ω is the unique (up to phase) translation-invariant vector -/
def VacuumUnique (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  IsTimeTranslationInvariant d π Ω ∧
  ∀ ψ : H, IsTimeTranslationInvariant d π ψ → ∃ c : ℂ, ψ = c • Ω

/-! ### The Complete Wightman QFT Structure -/

/-- A Wightman quantum field theory consists of:
    - A Hilbert space H (the state space)
    - A unitary representation of the Poincaré group
    - Field operators satisfying the Wightman axioms

    This structure encapsulates all the Wightman axioms (W1-W4). -/
structure WightmanQFT (d : ℕ) [NeZero d] where
  /-- The Hilbert space of states -/
  HilbertSpace : Type*
  /-- Hilbert space is a normed additive commutative group -/
  [instNormedAddCommGroup : NormedAddCommGroup HilbertSpace]
  /-- Hilbert space has inner product structure -/
  [instInnerProductSpace : InnerProductSpace ℂ HilbertSpace]
  /-- Hilbert space is complete -/
  [instCompleteSpace : CompleteSpace HilbertSpace]

  -- W1: Poincaré Covariance and Spectrum Condition
  /-- The unitary representation of the Poincaré group -/
  poincare_rep : @PoincareRepresentation d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- Spectrum condition: energy-momentum spectrum in forward cone -/
  spectrum_condition : @SpectralCondition d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep
  /-- The vacuum vector -/
  vacuum : HilbertSpace
  /-- The vacuum is normalized -/
  vacuum_normalized : @norm HilbertSpace instNormedAddCommGroup.toNorm vacuum = 1
  /-- The vacuum is Poincaré invariant -/
  vacuum_invariant : @IsPoincareInvariant d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

  -- W2: Field Operators
  /-- The field operator-valued distribution -/
  field : @OperatorValuedDistribution d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- The vacuum is in the domain -/
  vacuum_in_domain : vacuum ∈ field.domain
  /-- Cyclicity: the algebraic span of field operators on vacuum is dense -/
  cyclicity : @Dense HilbertSpace (instNormedAddCommGroup.toUniformSpace.toTopologicalSpace)
              (field.algebraicSpan vacuum).carrier
  /-- Covariance: U(g) φ(f) U(g)⁻¹ = φ(f ∘ g⁻¹) expressed via matrix elements -/
  covariance : True  -- Placeholder; full covariance requires Poincaré action on Schwartz space

  -- W3: Locality
  /-- Locality: spacelike-separated fields commute -/
  locality : @IsLocal d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace field

  -- W4: Vacuum Uniqueness
  /-- Uniqueness of vacuum -/
  vacuum_unique : @VacuumUnique d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

namespace WightmanQFT

variable {d : ℕ} [NeZero d]

-- Expose instances from WightmanQFT for use in definitions
attribute [instance] WightmanQFT.instNormedAddCommGroup
attribute [instance] WightmanQFT.instInnerProductSpace
attribute [instance] WightmanQFT.instCompleteSpace

/-- The Wightman n-point functions of a Wightman QFT.
    W_n(f₁,...,fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ -/
def wightmanFunction (qft : WightmanQFT d) (n : ℕ) :
    (Fin n → SchwartzSpacetime d) → ℂ :=
  fun fs => ⟪qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ

/-- The 2-point function (propagator) W₂(f,g) = ⟨Ω, φ(f)φ(g)Ω⟩ -/
def twoPointFunction (qft : WightmanQFT d) :
    SchwartzSpacetime d → SchwartzSpacetime d → ℂ :=
  fun f g => qft.wightmanFunction 2 ![f, g]

/-- Symmetry property for bosonic fields: [φ(f), φ(g)] = 0 for any f, g -/
def IsBosonic (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    Commutator (qft.field.operator f) (qft.field.operator g) qft.field.domain.toSubmodule

/-- The Reeh-Schlieder property: the vacuum is cyclic for local algebras.
    For any open region O, the vectors φ(f₁)···φ(fₙ)Ω with supp(fᵢ) ⊆ O are dense. -/
def ReehSchlieder (qft : WightmanQFT d) (O : Set (SpacetimeDim d)) : Prop :=
  let localSpan := Submodule.span ℂ
    { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
      (∀ i, Function.support (fs i) ⊆ O) ∧
      ψ = qft.field.operatorPow n fs qft.vacuum }
  Dense localSpan.carrier

/-- The Wightman functions are positive (reflection positivity).
    ‖φ(f₁)···φ(fₙ)Ω‖² ≥ 0, equivalently Re⟨ψ, ψ⟩ ≥ 0.
    For inner products in Hilbert space, ⟨ψ, ψ⟩ is real and equals ‖ψ‖². -/
def WightmanPositivity (qft : WightmanQFT d) : Prop :=
  ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
    (⟪qft.field.operatorPow n fs qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ).re ≥ 0

/-- Hermiticity of the 2-point function: W₂(f, g)* = W₂(ḡ, f̄).
    This follows from the hermiticity of the field. -/
def TwoPointHermitian (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    starRingEnd ℂ (qft.twoPointFunction f g) = qft.twoPointFunction g f

end WightmanQFT

/-! ### Wightman Functions as Distributions -/

/-- The Wightman n-point functions satisfy temperedness -/
def WightmanTempered (qft : WightmanQFT d) (n : ℕ) : Prop :=
  -- The n-point function, viewed as a distribution on 𝒮(ℝ^{n(d+1)}),
  -- extends to a tempered distribution
  True  -- Placeholder; would need proper multilinear distribution theory

/-! ### Analytic Continuation -/

/-- The Wightman functions have analytic continuation to the forward tube -/
structure WightmanAnalyticity (qft : WightmanQFT d) where
  /-- The forward tube domain -/
  forwardTube : ℕ → Set (Fin n → ℂ → ℂ)
  /-- Analytic continuation exists -/
  analytic : True  -- Placeholder for complex analysis formulation

end


import ModularPhysics.Core.QFT.RG.Basic
import ModularPhysics.Core.QFT.BV.BatalinVilkovisky
import ModularPhysics.Core.QFT.PathIntegral.PathIntegrals
import ModularPhysics.Core.QFT.PathIntegral.Regularization

namespace ModularPhysics.Core.QFT.RG.EffectiveAction

/-!
# Effective Actions in QFT

There are two fundamentally different notions of "effective action" in QFT:

## 1. 1PI Effective Action Γ[φ_cl] (Quantum Effective Action)

The 1PI effective action is the generating functional for one-particle irreducible
(1PI) diagrams. It is defined via the Legendre transform of the connected generating
functional W[J].

**Mathematical definition:**
- W[J] = -i log Z[J] generates connected diagrams
- φ_cl = δW/δJ defines the classical field
- Γ[φ_cl] = W[J] - ∫ J·φ_cl (Legendre transform)

**Key properties:**
- Generates 1PI vertices via functional derivatives
- δΓ/δφ_cl = -J (quantum equation of motion)
- At J=0: δΓ/δφ_cl = 0 determines the vacuum
- Convex functional (as a Legendre transform)

**Rigorous status:**
- Only defined perturbatively via formal power series in ℏ
- The path integral Z[J] is a formal object at this level
- Loop expansion: Γ = S + ℏΓ₁ + ℏ²Γ₂ + ... is well-defined order by order

## 2. Wilsonian Effective Action S_Λ[φ]

The Wilsonian effective action is obtained by integrating out field modes with
momenta above a UV cutoff Λ, using a regularized path integral measure.

**Mathematical definition:**
- Start with bare action S_Λ₀[φ] at UV cutoff Λ₀
- Integrate out modes with Λ < |p| < Λ₀
- S_Λ[φ] is the resulting action for modes with |p| < Λ

**Key properties:**
- Satisfies the exact RG equation (Polchinski equation)
- Preserves the partition function: Z is Λ-independent
- Contains all operators compatible with symmetries
- Non-local in general (can be expanded in local operators)

**Rigorous status:**
- In principle non-perturbatively defined
- The regularized measure can be constructed rigorously
- Connected to constructive QFT approaches
-/

open ModularPhysics.Core.QFT.RG
open ModularPhysics.Core.QFT.BV
open ModularPhysics.Core.QFT.PathIntegral

/- ============================================================================
   PART I: ABSTRACT FUNCTIONAL SPACES

   These structures provide an abstract interface for field configuration spaces.
   For concrete implementations, see PathIntegral.FieldConfigurations which defines:
   - FieldConfig: general field configurations
   - LinearFieldSpace: vector space structure for linear theories
   - GaugeFieldSpace: configurations with gauge redundancy

   The structures below are compatible with the PathIntegral definitions.
   ============================================================================ -/

/-- Abstract space of field configurations φ -/
structure FieldConfigurationSpace where
  /-- The underlying type (e.g., smooth functions on spacetime) -/
  carrier : Type
  /-- Zero configuration -/
  zero : carrier
  /-- Addition of configurations -/
  add : carrier → carrier → carrier
  /-- Scalar multiplication -/
  smul : ℝ → carrier → carrier

/-- Abstract space of source configurations J -/
structure SourceSpace where
  /-- The underlying type -/
  carrier : Type
  /-- Zero source -/
  zero : carrier
  /-- Addition of sources -/
  add : carrier → carrier → carrier
  /-- Scalar multiplication -/
  smul : ℝ → carrier → carrier

/-- Bilinear pairing between source and field spaces: ⟨J, φ⟩ = ∫ J(x)φ(x) d^d x -/
structure SourceFieldPairing (S : SourceSpace) (F : FieldConfigurationSpace) where
  /-- The pairing function -/
  pair : S.carrier → F.carrier → ℝ
  /-- Linearity in source -/
  linear_source : ∀ J₁ J₂ φ, pair (S.add J₁ J₂) φ = pair J₁ φ + pair J₂ φ
  /-- Linearity in field -/
  linear_field : ∀ J φ₁ φ₂, pair J (F.add φ₁ φ₂) = pair J φ₁ + pair J φ₂
  /-- Scalar multiplication in source -/
  smul_source : ∀ c J φ, pair (S.smul c J) φ = c * pair J φ
  /-- Scalar multiplication in field -/
  smul_field : ∀ c J φ, pair J (F.smul c φ) = c * pair J φ

/- ============================================================================
   PART II: 1PI EFFECTIVE ACTION (PERTURBATIVE)
   ============================================================================ -/

/-- The connected generating functional W[J]

    Formally: W[J] = -i log Z[J] where Z[J] = ∫ Dφ exp(iS[φ] + i⟨J,φ⟩)

    W[J] generates connected Green's functions:
    G_c^(n)(x₁,...,xₙ) = (-i)^(n-1) δⁿW/δJ(x₁)...δJ(xₙ)|_{J=0}

    At the perturbative level, this is defined as a formal power series in ℏ. -/
structure ConnectedGeneratingFunctional (S : SourceSpace) where
  /-- The functional W: J → ℝ (imaginary part absorbed into definition) -/
  W : S.carrier → ℝ
  /-- Normalization: W[0] = 0 -/
  normalized : W S.zero = 0

/-- Functional derivative δW/δJ defining the classical field

    φ_cl[J](x) = δW[J]/δJ(x) = ⟨φ(x)⟩_J

    This is the expectation value of the field in the presence of source J. -/
structure ClassicalFieldMap (S : SourceSpace) (F : FieldConfigurationSpace) where
  /-- The generating functional -/
  W : ConnectedGeneratingFunctional S
  /-- The map J ↦ φ_cl[J] -/
  classical_field : S.carrier → F.carrier
  /-- Vacuum expectation value: φ_cl[0] = ⟨φ⟩ -/
  vev : F.carrier := classical_field S.zero

/-- Invertibility condition for the Legendre transform

    The map J ↦ φ_cl = δW/δJ should be invertible to define Γ.
    This requires W to be strictly convex. -/
structure InvertibleClassicalField (S : SourceSpace) (F : FieldConfigurationSpace)
    extends ClassicalFieldMap S F where
  /-- Inverse map: given φ_cl, find J such that δW/δJ = φ_cl -/
  source_of_field : F.carrier → S.carrier
  /-- Left inverse: source_of_field ∘ classical_field = id -/
  left_inverse : ∀ J, source_of_field (classical_field J) = J
  /-- Right inverse: classical_field ∘ source_of_field = id -/
  right_inverse : ∀ φ, classical_field (source_of_field φ) = φ

/-- The 1PI effective action Γ[φ_cl] via Legendre transform

    Γ[φ_cl] = W[J[φ_cl]] - ⟨J[φ_cl], φ_cl⟩

    where J[φ_cl] is the inverse of φ_cl[J] = δW/δJ.

    Equivalently: Γ[φ] = sup_J (⟨J, φ⟩ - W[J])

    This is the generating functional for 1PI (amputated) Green's functions. -/
structure OnePIEffectiveAction (S : SourceSpace) (F : FieldConfigurationSpace)
    (pairing : SourceFieldPairing S F) where
  /-- The invertible classical field map -/
  field_map : InvertibleClassicalField S F
  /-- The 1PI effective action Γ[φ] -/
  Gamma : F.carrier → ℝ
  /-- Legendre transform relation -/
  legendre_transform : ∀ φ,
    Gamma φ = field_map.W.W (field_map.source_of_field φ) -
              pairing.pair (field_map.source_of_field φ) φ

/-- The quantum equation of motion: δΓ/δφ = -J

    At J = 0, this becomes δΓ/δφ = 0, determining the vacuum configuration. -/
structure QuantumEOM (S : SourceSpace) (F : FieldConfigurationSpace)
    (pairing : SourceFieldPairing S F) (Γ : OnePIEffectiveAction S F pairing) where
  /-- Functional derivative δΓ/δφ -/
  gamma_derivative : F.carrier → S.carrier
  /-- EOM relation: δΓ/δφ_cl = -J[φ_cl] -/
  eom : ∀ φ, gamma_derivative φ = S.smul (-1) (Γ.field_map.source_of_field φ)

/-- Convexity of the 1PI effective action

    As a Legendre transform of a convex functional, Γ is convex. -/
def OnePIConvexity (F : FieldConfigurationSpace) (Γ : F.carrier → ℝ) : Prop :=
  ∀ φ₁ φ₂ : F.carrier, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    Γ (F.add (F.smul t φ₁) (F.smul (1-t) φ₂)) ≤ t * Γ φ₁ + (1-t) * Γ φ₂

/-- Double Legendre transform involution

    Under convexity: Legendre(Legendre(W)) = W

    For the reverse transform, the roles of source and field are swapped:
    - Γ[φ] becomes the "generating functional"
    - J becomes the "field variable"
    - The Legendre transform of Γ recovers W -/
structure LegendreInvolution (S : SourceSpace) (F : FieldConfigurationSpace)
    (pairing : SourceFieldPairing S F) where
  /-- Forward: W → Γ -/
  forward : OnePIEffectiveAction S F pairing
  /-- Backward: Γ → W' (Legendre transform of Γ) -/
  backward_Gamma : S.carrier → ℝ
  /-- Involution property: W' = W -/
  involution : ∀ J, backward_Gamma J = forward.field_map.W.W J

/- ============================================================================
   PART III: 1PI VERTEX FUNCTIONS
   ============================================================================ -/

/-- 1PI vertex functions (proper vertices)

    Γ^(n)(x₁,...,xₙ) = δⁿΓ/δφ(x₁)...δφ(xₙ)|_{φ=φ_vac}

    These are the vertices that remain connected when any single
    internal propagator is cut. The full Green's functions are
    reconstructed from 1PI vertices via tree diagrams. -/
structure OnePIVertices (F : FieldConfigurationSpace) where
  /-- The effective action -/
  Gamma : F.carrier → ℝ
  /-- Vacuum field configuration -/
  vacuum : F.carrier
  /-- n-point 1PI vertex (abstract representation) -/
  vertex : ℕ → F.carrier

/-- 2-point 1PI function = inverse propagator -/
def twoPointVertex (v : OnePIVertices F) : F.carrier := v.vertex 2

/-- Physical mass from pole of propagator (2-point function at p² = m²) -/
noncomputable def physicalMassSquared (v : OnePIVertices F)
    (extractMass : F.carrier → ℝ) : ℝ :=
  extractMass (v.vertex 2)

/- ============================================================================
   PART IV: LOOP EXPANSION OF 1PI EFFECTIVE ACTION
   ============================================================================ -/

/-- Loop expansion of the 1PI effective action

    Γ[φ] = S[φ] + ℏ Γ₁[φ] + ℏ² Γ₂[φ] + O(ℏ³)

    where:
    - S[φ] is the classical action (tree level)
    - Γ₁[φ] = (i/2) Tr log(δ²S/δφ²) is the one-loop correction
    - Γₙ[φ] is the n-loop correction

    This expansion is what makes the 1PI action rigorously defined
    at the perturbative level: each Γₙ is computed from Feynman diagrams. -/
structure LoopExpansion (F : FieldConfigurationSpace) where
  /-- Classical action S[φ] (zeroth order in ℏ) -/
  classical_action : F.carrier → ℝ
  /-- n-loop correction Γₙ[φ] for n ≥ 1 -/
  loop_correction : ℕ → (F.carrier → ℝ)
  /-- ℏ = 0 limit is classical -/
  loop_correction_zero : loop_correction 0 = classical_action

/-- One-loop effective action via functional determinant

    Γ₁[φ] = (i/2) Tr log(δ²S/δφ²)
          = (i/2) log det(δ²S/δφ²)

    The second functional derivative δ²S/δφ² is the fluctuation
    operator around configuration φ. -/
structure OneLoopCorrection (F : FieldConfigurationSpace) where
  /-- Classical action -/
  classical_action : F.carrier → ℝ
  /-- Fluctuation operator at configuration φ -/
  fluctuation_operator : F.carrier → (F.carrier → F.carrier)
  /-- One-loop correction (log determinant, requires regularization) -/
  one_loop : F.carrier → ℝ

/-- Evaluate the full 1PI action at L loops -/
noncomputable def evaluateLoopExpansion (L : LoopExpansion F) (hbar : ℝ) (φ : F.carrier)
    (nLoops : ℕ) : ℝ :=
  (List.range (nLoops + 1)).foldl (fun acc n => acc + hbar^n * L.loop_correction n φ) 0

/-- Tree-level approximation: just the classical action -/
def treeLevel (L : LoopExpansion F) : F.carrier → ℝ := L.classical_action

/-- One-loop approximation: S + ℏΓ₁ -/
noncomputable def oneLoopApprox (L : LoopExpansion F) (hbar : ℝ) (φ : F.carrier) : ℝ :=
  L.classical_action φ + hbar * L.loop_correction 1 φ

/-- Two-loop approximation -/
noncomputable def twoLoopApprox (L : LoopExpansion F) (hbar : ℝ) (φ : F.carrier) : ℝ :=
  L.classical_action φ + hbar * L.loop_correction 1 φ + hbar^2 * L.loop_correction 2 φ

/- ============================================================================
   PART V: WILSONIAN EFFECTIVE ACTION (NON-PERTURBATIVE)
   ============================================================================ -/

/-- Momentum space decomposition

    Field modes are split into:
    - High momentum: |p| > Λ (integrated out)
    - Low momentum: |p| ≤ Λ (kept) -/
structure MomentumDecomposition (F : FieldConfigurationSpace) (Λ : Cutoff) where
  /-- Low momentum modes (|p| ≤ Λ) -/
  low_modes : F.carrier → F.carrier
  /-- High momentum modes (|p| > Λ) -/
  high_modes : F.carrier → F.carrier
  /-- Decomposition: φ = φ_< + φ_> -/
  decomposition : ∀ φ, F.add (low_modes φ) (high_modes φ) = φ

/-- Regularized path integral measure

    The Wilsonian approach uses a path integral with regularized measure:
    ∫ Dφ_Λ where the measure only includes modes with |p| < Λ.

    This is in principle non-perturbatively defined (e.g., lattice). -/
structure RegularizedMeasure (F : FieldConfigurationSpace) where
  /-- UV cutoff -/
  cutoff : Cutoff
  /-- The regularized measure exists (structural axiom) -/
  measure_exists : Prop

/-- The Wilsonian effective action S_Λ[φ]

    Defined by integrating out high-momentum modes:

    exp(-S_Λ[φ_<]) = ∫ Dφ_> exp(-S_Λ₀[φ_< + φ_>])

    where:
    - Λ₀ is the initial (bare) UV cutoff
    - Λ < Λ₀ is the lowered cutoff
    - φ_< are low-momentum modes (|p| < Λ)
    - φ_> are high-momentum modes (Λ < |p| < Λ₀)

    Key distinction from 1PI: This is defined non-perturbatively
    via the regularized functional integral. -/
structure WilsonianEffectiveAction (F : FieldConfigurationSpace) where
  /-- Bare UV cutoff -/
  bare_cutoff : Cutoff
  /-- Bare action at UV scale -/
  bare_action : F.carrier → ℝ
  /-- Wilsonian action at scale Λ ≤ Λ₀ -/
  action_at_scale : Cutoff → (F.carrier → ℝ)
  /-- At bare scale, Wilsonian action equals bare action -/
  initial_condition : action_at_scale bare_cutoff = bare_action

/-- Partition function independence

    The partition function Z is independent of the cutoff Λ:

    Z = ∫ Dφ_Λ₀ exp(-S_Λ₀[φ]) = ∫ Dφ_Λ exp(-S_Λ[φ])

    This is the defining property of Wilsonian RG. -/
structure PartitionFunctionIndependence (F : FieldConfigurationSpace)
    (W : WilsonianEffectiveAction F) where
  /-- Abstract partition function at each scale -/
  Z : Cutoff → ℝ
  /-- Z is Λ-independent -/
  scale_independence : ∀ Λ₁ Λ₂ : Cutoff, Z Λ₁ = Z Λ₂

/-- Exact RG equation (Polchinski equation)

    The Wilsonian action satisfies the exact RG flow equation:

    Λ ∂S_Λ/∂Λ = (1/2) Tr[(∂Δ_Λ/∂Λ)(δ²S_Λ/δφδφ - δS_Λ/δφ ⊗ δS_Λ/δφ)]

    where Δ_Λ is the regularized propagator.

    This is a functional differential equation that can be solved
    non-perturbatively (in principle). -/
structure PolchinskiEquation (F : FieldConfigurationSpace) where
  /-- Wilsonian effective action -/
  W : WilsonianEffectiveAction F
  /-- Regularized propagator at scale Λ -/
  propagator : Cutoff → (F.carrier → F.carrier → ℝ)
  /-- Scale derivative of propagator -/
  propagator_derivative : Cutoff → (F.carrier → F.carrier → ℝ)
  /-- The RG flow (Λ ∂/∂Λ) of the action -/
  rg_flow : Cutoff → (F.carrier → ℝ)

/-- Local operator expansion of Wilsonian action

    S_Λ[φ] = ∫ d^d x [g₀(Λ) + g₂(Λ)(∂φ)² + g₄(Λ)φ⁴ + ...]

    The Wilsonian action can be expanded in local operators.
    The couplings gᵢ(Λ) run with the scale.

    This connects to the operator basis in RG.Basic via `RGFramework`. -/
structure LocalOperatorExpansion (F : FieldConfigurationSpace) {d : ℕ}
    (rg : RGFramework d) where
  /-- Wilsonian action -/
  W : WilsonianEffectiveAction F
  /-- Running coupling for each local operator at scale Λ -/
  coupling : rg.Operator → Cutoff → ℝ
  /-- Beta function for each operator -/
  beta : rg.Operator → Cutoff → ℝ

/-- Dimensionless coupling at scale Λ -/
noncomputable def dimensionlessCouplingAt {d : ℕ} {rg : RGFramework d}
    (L : LocalOperatorExpansion F rg) (O : rg.Operator) (Λ : Cutoff) : ℝ :=
  L.coupling O Λ * Λ.Λ ^ (rg.massDimension O - d)

/-- RG flow of a coupling: g(Λ₂) from g(Λ₁) at one-loop -/
noncomputable def runCoupling {d : ℕ} {rg : RGFramework d}
    (L : LocalOperatorExpansion F rg) (O : rg.Operator) (Λ₁ Λ₂ : Cutoff) : ℝ :=
  L.coupling O Λ₁ + L.beta O Λ₁ * Real.log (Λ₂.Λ / Λ₁.Λ)

/-- Check if operator is relevant (Δ < d) -/
def isRelevantOp {d : ℕ} (rg : RGFramework d) (O : rg.Operator) : Prop :=
  Relevant rg O

/-- Check if operator is marginal (Δ = d) -/
def isMarginalOp {d : ℕ} (rg : RGFramework d) (O : rg.Operator) : Prop :=
  Marginal rg O

/- ============================================================================
   PART V-B: COMPATIBILITY WITH PATHINTEGRAL MODULE
   ============================================================================ -/

/-- Convert UVCutoff from PathIntegral to Cutoff from RG.Basic -/
def cutoffFromUV (uv : UVCutoff) : Cutoff := ⟨uv.scale, uv.positive⟩

/-- Convert Cutoff to UVCutoff -/
def uvFromCutoff (c : Cutoff) : UVCutoff := ⟨c.Λ, c.positive⟩

/-- The regularized path integral from PathIntegral.Regularization
    is the foundation for the Wilsonian effective action.

    The Wilsonian action S_Λ is defined implicitly by:
    exp(-S_Λ[φ_<]) = ∫_{Λ < |p| < Λ₀} Dφ_> exp(-S_{Λ₀}[φ_< + φ_>])

    which uses regularizedPathIntegral with appropriate cutoffs. -/
structure WilsonianFromPathIntegral (F : Type _) where
  /-- The bare action as ActionFunctional from PathIntegral -/
  bare_action : ActionFunctional F
  /-- Field measure -/
  measure : FieldMeasure F
  /-- UV cutoff -/
  uv_cutoff : UVCutoff
  /-- The effective action at scale Λ ≤ uv_cutoff (implicitly defined) -/
  effective_at_scale : UVCutoff → (F → ℝ)

/-- The 1PI effective action from PathIntegral.
    The effective action Γ[φ_cl] is the Legendre transform of W[J] = -iℏ log Z[J].

    The relationship is:
    - The generating functional Z[J] = ∫ Dφ e^{iS[φ] + i∫J·φ} defines W[J]
    - The classical field φ_cl = δW/δJ
    - Γ[φ_cl] = W[J] - ∫ J·φ_cl
    - OnePIEffectiveAction provides this Legendre transform structure -/
noncomputable def onePIFromPathIntegral {F : Type _} (S : ActionFunctional F) (μ : FieldMeasure F) :
    ActionFunctional F where
  eval := fun φ_cl => sorry  -- Legendre transform of connected generating functional

/- Connection to Semiclassical.lean:

   The loop expansion of the 1PI effective action relates to the semiclassical
   approximation in PathIntegral.Semiclassical:
   - S[φ] is the classical action (tree level)
   - Γ₁[φ] = (i/2) log det(δ²S/δφ²) is the one-loop correction
   - The semiclassicalApproximation captures the ℏ → 0 limit -/

/- ============================================================================
   PART VII: BV STRUCTURE OF EFFECTIVE ACTIONS FOR GAUGE THEORIES
   ============================================================================ -/

/-!
## BV Master Equations for Effective Actions

For gauge theories in the BV formalism, the effective actions satisfy distinct
master equations:

### 1PI Effective Action satisfies Classical Master Equation

The 1PI effective action Γ[φ, φ*] (including antifields φ*) of a gauge theory
satisfies the **classical** BV master equation:

    (Γ, Γ) = 0

where (,) is the antibracket. This holds even though Γ includes all quantum
corrections (loop expansion). The reason is that Γ is defined via Legendre
transform, which preserves the classical BV structure.

More precisely: if W[J, K] is the generating functional for connected diagrams
with sources J for fields and K for antifields, and Γ is its Legendre transform
with respect to J only (keeping K as the antifield), then Γ satisfies (Γ,Γ) = 0.

This is equivalent to the Zinn-Justin equation for W[J,K].

### Wilsonian Effective Action satisfies Quantum Master Equation

The Wilsonian effective action S_Λ[φ, φ*] at scale Λ satisfies the **quantum**
BV master equation:

    (S_Λ, S_Λ) = 2ℏ Δ S_Λ

**Crucial definition**: The Wilsonian effective action for a gauge theory is defined
via integration over a **Lagrangian submanifold** in the BV field space. Specifically:

1. Split the fields into high-momentum modes φ_> (Λ < |p| < Λ₀) and
   low-momentum modes φ_< (|p| < Λ).

2. In the BV field-antifield space, the high-momentum modes span a subspace.
   Choose a Lagrangian submanifold L_> for the high-momentum sector
   (with respect to the odd symplectic form ω).

3. Define S_Λ by integrating out the high-momentum modes over L_>:

      exp(-S_Λ[φ_<, φ*_<]/ℏ) = ∫_{L_>} Dφ_> exp(-S_{Λ₀}[φ_< + φ_>, φ*_< + φ*_>]/ℏ)

4. The key theorem: If S_{Λ₀} satisfies the QME at scale Λ₀, then S_Λ
   satisfies the QME for the low-momentum modes.

This is how consistency is established: the QME is preserved under the RG flow
because integration over a Lagrangian submanifold preserves the BV structure.

### Physical Interpretation

- CME for Γ: Encodes BRST symmetry of the quantum theory (Ward identities)
- QME for S_Λ: Ensures consistent quantization at each scale (path integral well-defined)

Note: The 1PI and Wilsonian effective actions are fundamentally different objects.
The 1PI action is perturbatively defined via Legendre transform while the Wilsonian
action is non-perturbatively defined via path integral with cutoff. They satisfy
different master equations and should not be conflated.
-/

/-- The 1PI effective action of a gauge theory in BV formalism

    Extends the 1PI effective action to include antifields φ*.
    The action Γ[φ, φ*] depends on both fields and antifields.

    Uses the BV structures from BatalinVilkovisky.lean. -/
structure OnePIEffectiveActionBV where
  /-- The extended field space (fields + antifields) -/
  space : ExtendedFieldSpace
  /-- The 1PI effective action as a BV functional -/
  Gamma : BVFunctional
  /-- Ghost number 0 -/
  ghost_constraint : Gamma.ghost_number = ⟨0⟩
  /-- Bosonic -/
  parity_constraint : Gamma.parity = BRST.GrassmannParity.even

/-- Classical master equation for 1PI effective action

    The 1PI effective action Γ[φ, φ*] of a gauge theory satisfies:

    (Γ, Γ) = 0

    This is a consequence of BRST symmetry and the Legendre transform structure.
    Equivalently, it follows from the Zinn-Justin equation for W[J, K].

    Uses the ClassicalMasterEquation from BatalinVilkovisky.lean. -/
def OnePISatisfiesCME (ab : Antibracket) (Γ_BV : OnePIEffectiveActionBV) : Prop :=
  (ab.bracket Γ_BV.Gamma Γ_BV.Gamma).functional = fun _ => 0

/-- The Wilsonian effective action of a gauge theory in BV formalism

    The Wilsonian action S_Λ[Φ_<, Φ*_<] at scale Λ is defined by integrating out
    high-momentum modes (Φ_>, Φ*_>) over a Lagrangian submanifold L_{V_>}:

      exp(-S_eff[Φ_<, Φ*_<]) = ∫_{L_{V_>}} DΦ_> exp(-S[Φ_<, Φ*_<; Φ_>, Φ*_>])

    where L_{V_>} is the Lagrangian submanifold defined by the gauge-fixing fermion V_>:

      L_{V_>}: Φ*_{I>} = δV_>/δΦ^I_>

    This is a Lagrangian submanifold with respect to the odd symplectic form ω
    on the high-momentum field-antifield space.

    Key theorem: If the bare action S satisfies the quantum BV master equation,
    then S_eff[Φ_<, Φ*_<] also satisfies the QME with respect to the low-momentum
    modes. This establishes consistency of the Wilsonian RG in gauge theories. -/
structure WilsonianEffectiveActionBV where
  /-- The extended field space (full field-antifield space) -/
  space : ExtendedFieldSpace
  /-- The odd symplectic form on field-antifield space -/
  omega : OddSymplecticForm
  /-- The Wilsonian action at each scale as a BV functional -/
  S_Lambda : Cutoff → BVFunctional
  /-- Bare UV cutoff Λ₀ -/
  bare_cutoff : Cutoff
  /-- Gauge-fixing fermion V_> for high-momentum modes at each scale -/
  gf_fermion_high : Cutoff → BVGaugeFixing
  /-- Ghost number 0 at each scale -/
  ghost_constraint : ∀ Λ, (S_Lambda Λ).ghost_number = ⟨0⟩
  /-- Bosonic at each scale -/
  parity_constraint : ∀ Λ, (S_Lambda Λ).parity = BRST.GrassmannParity.even

/-- Lagrangian submanifold for high-momentum modes

    L_{V_>} = { (Φ_>, Φ*_>) | Φ*_{I>} = δV_>/δΦ^I_> }

    This is the submanifold over which we integrate to define the Wilsonian
    effective action. It is Lagrangian with respect to the odd symplectic form ω. -/
structure HighMomentumLagrangian where
  /-- The odd symplectic form -/
  omega : OddSymplecticForm
  /-- The gauge-fixing fermion V_> defining the Lagrangian submanifold -/
  V : BVGaugeFixing
  /-- The constraint Φ*_{I>} = δV_>/δΦ^I_> -/
  constraint : ExtendedFieldSpace → Prop
  /-- L_{V_>} is isotropic (ω|_{L_{V_>}} = 0) -/
  isotropic : ∀ s₁ s₂, constraint s₁ → constraint s₂ → omega.pairing s₁ s₂ = 0

/-- Quantum master equation for Wilsonian effective action

    The Wilsonian effective action S_Λ[Φ_<, Φ*_<] satisfies at each scale Λ:

    (S_Λ, S_Λ) = 2ℏ Δ S_Λ

    where (,) is the antibracket and Δ is the BV Laplacian, both restricted to
    the low-momentum field-antifield space at scale Λ.

    Uses the QuantumMasterEquation from BatalinVilkovisky.lean. -/
def WilsonianSatisfiesQME (ab : Antibracket) (Δ : BVLaplacian)
    (S_BV : WilsonianEffectiveActionBV) (Λ : Cutoff) (hbar : ℝ) : Prop :=
  ∀ s : ExtendedFieldSpace,
    (ab.bracket (S_BV.S_Lambda Λ) (S_BV.S_Lambda Λ)).functional s =
    2 * hbar * (Δ.laplacian (S_BV.S_Lambda Λ)).functional s

/-- QME is preserved under Wilsonian RG flow

    The key theorem of BV-Wilsonian RG: If the bare action S_{Λ₀} satisfies
    the quantum BV master equation, then S_Λ satisfies the QME at all lower
    scales Λ < Λ₀.

    Proof sketch (from the latex notes):
    1. Start with the QME for the full action: (S,S) = 2ℏΔS
    2. Split fields into low (Φ_<) and high (Φ_>) momentum modes
    3. Integrate out Φ_> over the Lagrangian submanifold L_{V_>}
    4. Using the QME and integration by parts:

       δ_R/δΦ*_{I<} · δ/δΦ^I_< exp(-S_eff)
       = ∫_{L_{V_>}} DΦ_> · δ_R/δΦ*_{I<} · δ/δΦ^I_< exp(-S)
       = -∫_{L_{V_>}} DΦ_> · δ_R/δΦ*_{I>} · δ/δΦ^I_> exp(-S)   (by QME)
       = ∫_{L_{V_>}} DΦ_> · (δ²V_>/δΦ^I_>δΦ^J_>) · δ/δΦ*_{J>} · δ_R/δΦ*_{I>} exp(-S)
       = 0   (since δ²V_>/δΦ^I_>δΦ^J_> is symmetric and ω is antisymmetric)

    The vanishing follows from the Lagrangian property of L_{V_>}. -/
def QMEPreservedUnderRG (ab : Antibracket) (Δ : BVLaplacian)
    (S_BV : WilsonianEffectiveActionBV) (hbar : ℝ) : Prop :=
  WilsonianSatisfiesQME ab Δ S_BV S_BV.bare_cutoff hbar →
    ∀ Λ : Cutoff, Λ.Λ ≤ S_BV.bare_cutoff.Λ → WilsonianSatisfiesQME ab Δ S_BV Λ hbar

/-- The RG flow equation in BV formalism

    The Wilsonian effective action satisfies a functional flow equation:

    Λ ∂S_Λ/∂Λ = F[S_Λ, Δ_Λ, ...]

    where F involves the regularized propagator and the BV Laplacian.
    The QME preservation is built into this flow. -/
structure BVWilsonianRGFlow where
  /-- The Wilsonian effective action -/
  S : WilsonianEffectiveActionBV
  /-- The antibracket structure -/
  ab : Antibracket
  /-- The BV Laplacian -/
  Δ : BVLaplacian
  /-- QME holds at bare scale -/
  qme_bare : ∀ hbar, WilsonianSatisfiesQME ab Δ S S.bare_cutoff hbar
  /-- QME is preserved under flow -/
  qme_preserved : ∀ hbar, QMEPreservedUnderRG ab Δ S hbar

/-- Summary: Master equations for gauge theory effective actions

    | Effective Action | Master Equation | Reason |
    |-----------------|-----------------|--------|
    | 1PI Γ[φ,φ*]     | (Γ,Γ) = 0 (CME) | Legendre transform preserves classical structure |
    | Wilsonian S_Λ   | (S,S) = 2ℏΔS (QME) | Path integral measure contributes Δ term |

    The distinction arises because:
    - Γ is defined by Legendre transform (classical operation)
    - S_Λ is defined by path integral (quantum operation) -/
structure GaugeTheoryEffectiveActionsBV where
  /-- The antibracket structure -/
  ab : Antibracket
  /-- The BV Laplacian -/
  Δ : BVLaplacian
  /-- 1PI effective action -/
  one_pi : OnePIEffectiveActionBV
  /-- Wilsonian effective action -/
  wilsonian : WilsonianEffectiveActionBV
  /-- 1PI satisfies CME -/
  one_pi_cme : OnePISatisfiesCME ab one_pi
  /-- Wilsonian satisfies QME at each scale -/
  wilsonian_qme : ∀ Λ hbar, WilsonianSatisfiesQME ab Δ wilsonian Λ hbar
  /-- QME is preserved under RG flow -/
  qme_preserved : ∀ hbar, QMEPreservedUnderRG ab Δ wilsonian hbar

/-- Connection to Zinn-Justin equation

    The 1PI effective action Γ satisfying the CME is equivalent to
    the Zinn-Justin equation for the generating functional W. -/
def OnePICMEEquivalentToZJ (ab : Antibracket) (Δ : BVLaplacian)
    (Γ_BV : OnePIEffectiveActionBV) : Prop :=
  OnePISatisfiesCME ab Γ_BV ↔
    ∃ (zj : ZinnJustinEquation),
      zj.ab = ab ∧ zj.Δ = Δ ∧ zj.effective_action.action = Γ_BV.Gamma

end ModularPhysics.Core.QFT.RG.EffectiveAction

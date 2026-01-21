import ModularPhysics.Core.QFT.RG.Basic

namespace ModularPhysics.Core.QFT.RG.Wilsonian

/-!
# Wilsonian Renormalization Group

The Wilsonian approach to RG integrates out high-momentum modes shell by shell,
generating an effective action S_Λ[φ] that depends on the cutoff Λ.

## Key concepts:

1. **Wilsonian effective action S_Λ[φ]**: Contains all operators consistent
   with symmetries, with scale-dependent Wilson coefficients.

2. **Exact RG equation (Polchinski/Wetterich)**: Describes how S_Λ evolves
   as Λ is lowered. This is exact - no perturbation theory required.

3. **Locality**: The effective action remains quasi-local (expandable in
   local operators) under RG flow.

4. **Universality**: Different UV theories can flow to the same IR physics.

## Comparison with Gell-Mann Low:

- Wilsonian: Conceptually clear, non-perturbative, but requires specifying a cutoff
- Gell-Mann Low: Perturbative, cutoff-independent, more directly connected to observables

For gauge theories, the Wilsonian approach requires care to preserve gauge
invariance - see the BV formalism.
-/

open ModularPhysics.Core.QFT.RG

set_option linter.unusedVariables false

/- ============= WILSONIAN EFFECTIVE ACTION ============= -/

/-- Field configuration space (abstractly, maps from spacetime to field values) -/
structure FieldSpaceElement (d : ℕ) where
  data : Unit

/-- Field space type -/
abbrev FieldSpace (d : ℕ) := FieldSpaceElement d

/-- Wilsonian effective action at cutoff Λ

    S_Λ[φ] = ∫ d^d x ∑_i g_i(Λ) O_i(φ(x))

    This is a functional of the field configuration, depending on the cutoff. -/
structure WilsonianAction (d : ℕ) where
  /-- The cutoff scale -/
  cutoff : Cutoff
  /-- The action functional -/
  action : FieldSpace d → ℝ
  /-- Wilson coefficients for each operator -/
  coefficients : LocalOperator d → ℝ

/-- The Wilson coefficient for operator O at scale Λ -/
def wilsonCoeff {d : ℕ} (S : WilsonianAction d) (O : LocalOperator d) : ℝ :=
  S.coefficients O

/-- Dimensionless Wilson coefficient -/
noncomputable def dimlessWilsonCoeff {d : ℕ}
    (S : WilsonianAction d) (O : LocalOperator d) : ℝ :=
  S.coefficients O * S.cutoff.Λ ^ (massDimension O - d)

/- ============= EXACT RG FLOW ============= -/

/-- Infinitesimal RG transformation

    Lowering the cutoff Λ → Λ - δΛ integrates out modes in the momentum
    shell Λ - δΛ < |p| < Λ, modifying the effective action. -/
structure RGStep (d : ℕ) where
  /-- Initial action -/
  initial : WilsonianAction d
  /-- Final action (at slightly lower cutoff) -/
  final : WilsonianAction d
  /-- The cutoff decreased -/
  cutoff_decreased : final.cutoff.Λ < initial.cutoff.Λ

/-- Polchinski equation (schematic form)

    -Λ ∂S_Λ/∂Λ = (1/2) Tr[(∂_Λ K) · G₀ · (δ²S/δφ² - δS/δφ · δS/δφ)]

    where:
    - K is the cutoff function
    - G₀ is the free propagator
    - The functional derivatives are with respect to the field

    This is the exact RG equation - no approximations. -/
structure PolchinskiFlow (d : ℕ) where
  /-- Family of actions parametrized by cutoff -/
  actions : Scale → WilsonianAction d
  /-- Cutoff function used -/
  regulator : CutoffFunction
  /-- The flow satisfies the Polchinski equation -/
  satisfies_equation : Prop

/-- Wetterich equation (alternative exact RG formulation)

    Uses the effective average action Γ_k (Legendre transform of W_k).
    ∂_t Γ_k = (1/2) Tr[(∂_t R_k) · (Γ_k^(2) + R_k)^(-1)]

    where t = log(k/k₀) and R_k is the regulator. -/
structure WetterichFlow (d : ℕ) where
  /-- Effective average action at each scale -/
  effective_action : Scale → FieldSpace d → ℝ
  /-- Regulator function R_k -/
  regulator : Scale → ℝ → ℝ
  /-- Satisfies the Wetterich equation -/
  satisfies_equation : Prop

/- ============= LOCALITY AND DERIVATIVE EXPANSION ============= -/

/-- Derivative expansion of the effective action

    S_Λ[φ] = ∫ d^d x [V(φ) + (1/2)Z(φ)(∂φ)² + O(∂⁴)]

    At each order in derivatives, we have a function of the field (potential,
    wave function renormalization, etc.). -/
structure DerivativeExpansion (d : ℕ) where
  /-- Effective potential V(φ) -/
  potential : ℝ → ℝ
  /-- Wave function renormalization Z(φ) -/
  wavefunction_renorm : ℝ → ℝ
  /-- Higher derivative terms (truncated) -/
  higher_order : ℕ → (ℝ → ℝ)

/-- Local potential approximation (LPA): keep only V(φ), set Z = 1

    The simplest non-trivial truncation. Already captures fixed points
    and critical exponents qualitatively. -/
structure LPA (d : ℕ) where
  /-- The potential at each scale -/
  potential : Scale → (ℝ → ℝ)
  /-- Flow equation for V -/
  flow_equation : Prop

/-- LPA' approximation: LPA plus running Z(k)

    Include wave function renormalization but keep it field-independent. -/
structure LPAprime (d : ℕ) where
  potential : Scale → (ℝ → ℝ)
  Z : Scale → ℝ
  flow_equation : Prop

/- ============= INTEGRATING OUT ============= -/

/-- Integrating out high-momentum modes between Λ_UV and Λ_IR

    Given a UV theory at scale Λ_UV, compute the effective theory at Λ_IR < Λ_UV
    by path-integrating over modes with Λ_IR < |p| < Λ_UV. -/
structure ModeIntegration (d : ℕ) where
  /-- UV action -/
  uv_action : WilsonianAction d
  /-- IR action -/
  ir_action : WilsonianAction d
  /-- Scale separation -/
  scale_separation : ir_action.cutoff.Λ < uv_action.cutoff.Λ
  /-- The IR action is obtained by integrating out modes -/
  integration_condition : Prop

/- ============= WILSONIAN RG THEORY ============= -/

/-- Structure for Wilsonian RG theory -/
structure WilsonianRGTheory where
  /-- Power counting for irrelevant operators
      An operator of dimension Δ > d has Wilson coefficient that scales as
      g(Λ_IR) ~ g(Λ_UV) · (Λ_IR/Λ_UV)^(Δ-d) -/
  irrelevant_suppression : ∀ {d : ℕ} (mi : ModeIntegration d)
    (O : LocalOperator d) (h : Irrelevant O),
    ∃ C : ℝ, |wilsonCoeff mi.ir_action O| ≤
      C * |wilsonCoeff mi.uv_action O| *
      (mi.ir_action.cutoff.Λ / mi.uv_action.cutoff.Λ) ^ (massDimension O - d)

/-- Wilsonian RG theory holds -/
axiom wilsonianRGTheoryD : WilsonianRGTheory

/-- Power counting for irrelevant operators

    An operator of dimension Δ > d has Wilson coefficient that scales as
    g(Λ_IR) ~ g(Λ_UV) · (Λ_IR/Λ_UV)^(Δ-d) -/
theorem irrelevant_suppression {d : ℕ} (mi : ModeIntegration d)
    (O : LocalOperator d) (h : Irrelevant O) :
  ∃ C : ℝ, |wilsonCoeff mi.ir_action O| ≤
    C * |wilsonCoeff mi.uv_action O| *
    (mi.ir_action.cutoff.Λ / mi.uv_action.cutoff.Λ) ^ (massDimension O - d) :=
  wilsonianRGTheoryD.irrelevant_suppression mi O h

/- ============= UNIVERSALITY ============= -/

/-- Universality class

    A set of UV theories that flow to the same IR fixed point.
    The universal behavior is determined by the relevant operators at the
    IR fixed point. -/
structure UniversalityClass (d : ℕ) where
  /-- The IR fixed point defining the class -/
  ir_fixed_point : CouplingConfig d
  /-- It is indeed a fixed point -/
  is_fixed : FixedPoint ir_fixed_point
  /-- The relevant operators at this fixed point -/
  relevant_ops : Set (LocalOperator d)
  /-- Relevant ops are those with Δ < d at the fixed point -/
  relevant_criterion : ∀ O ∈ relevant_ops,
    scalingDimension O ir_fixed_point < d

/-- Critical exponents from scaling dimensions

    The critical exponent ν_O for operator O is related to its scaling dimension:
    ν_O = 1/(d - Δ_O) for relevant operators -/
noncomputable def criticalExponent {d : ℕ}
    (O : LocalOperator d) (fp : CouplingConfig d) : ℝ :=
  1 / (d - scalingDimension O fp)

/-- Universality: different microscopic theories in the same class give the same
    critical exponents, because critical exponents are determined solely by
    the IR fixed point. -/
noncomputable def universalCriticalExponent {d : ℕ} (uc : UniversalityClass d)
    (O : LocalOperator d) : ℝ :=
  criticalExponent O uc.ir_fixed_point

end ModularPhysics.Core.QFT.RG.Wilsonian

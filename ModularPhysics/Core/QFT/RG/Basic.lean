import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ModularPhysics.Core.QFT.RG

set_option linter.unusedVariables false

/-!
# Renormalization Group: Basic Concepts

This module defines the foundational concepts of the renormalization group:
- Energy/momentum scales and cutoffs
- Local operators and their mass dimensions
- Operator classification (relevant, marginal, irrelevant)
- Beta functions and RG flow
- Fixed points and anomalous dimensions

These concepts are common to both Wilsonian and Gell-Mann Low approaches.
-/

/-- Energy/momentum scale (positive real number representing an energy scale) -/
abbrev Scale := ℝ

/- ============= CUTOFFS ============= -/

/-- A momentum cutoff scale Λ > 0 -/
structure Cutoff where
  Λ : Scale
  positive : Λ > 0

/-- Smooth cutoff function K(p²/Λ²)

    Regulates high-momentum modes smoothly. Properties:
    - K(0) = 1 (no suppression at low momenta)
    - K(x) → 0 as x → ∞ (suppresses high momenta)

    Common choices: exp(-x), 1/(1+x)^n, θ(1-x) (hard cutoff) -/
structure CutoffFunction where
  /-- The cutoff function K: ℝ → ℝ -/
  eval : ℝ → ℝ
  /-- Normalization at zero -/
  at_zero : eval 0 = 1
  /-- Decay at infinity -/
  decay : ∀ ε > 0, ∃ M, ∀ x > M, eval x < ε

/- ============= LOCAL OPERATORS AND RG FRAMEWORK ============= -/

/-- RG framework: bundles the data needed for renormalization group analysis
    in d spacetime dimensions.

    This includes local operators with their dimensions, products, beta functions,
    anomalous dimensions, and flow data. All physical content that was previously
    spread across axioms is now bundled here. -/
structure RGFramework (d : ℕ) where
  /-- Type of local operators (built from fields and derivatives at a point) -/
  Operator : Type*
  /-- Mass (engineering) dimension of a local operator.
      Under rescaling x → λx, an operator O of dimension Δ scales as O → λ^(-Δ) O. -/
  massDimension : Operator → ℝ
  /-- Identity operator (dimension 0) -/
  identityOp : Operator
  /-- Product of local operators at coincident points -/
  operatorProduct : Operator → Operator → Operator
  /-- Identity has dimension 0 -/
  identity_dimension : massDimension identityOp = 0
  /-- Dimension of product is sum of dimensions (at classical level) -/
  dimension_additive : ∀ (O₁ O₂ : Operator),
    massDimension (operatorProduct O₁ O₂) = massDimension O₁ + massDimension O₂
  /-- Beta function β_O(g) for operator O.
      β_O = μ ∂g_O/∂μ describes how dimensionless coupling flows with scale. -/
  betaFunction : Operator → (Operator → ℝ) → ℝ
  /-- Anomalous dimension γ_O at a fixed point.
      At a fixed point, the full scaling dimension is Δ = Δ_classical + γ. -/
  anomalousDimension : Operator → (Operator → ℝ) → ℝ
  /-- UV limit of an RG trajectory (as μ → ∞) -/
  uvLimit : (Scale → (Operator → ℝ)) → (Operator → ℝ)
  /-- IR limit of an RG trajectory (as μ → 0) -/
  irLimit : (Scale → (Operator → ℝ)) → (Operator → ℝ)
  /-- Stability matrix for linearized RG near a fixed point -/
  stabilityMatrix : (Operator → ℝ) → Operator → Operator → ℝ
  /-- The free theory (all couplings zero) is always a fixed point -/
  gaussian_is_fixed_point : ∀ (O : Operator),
    betaFunction O (fun _ => 0) = 0
  /-- At the Gaussian fixed point, anomalous dimensions vanish -/
  gaussian_no_anomalous : ∀ (O : Operator),
    anomalousDimension O (fun _ => 0) = 0
  /-- Eigenvalue of stability matrix = scaling dimension - d -/
  stability_eigenvalue_relation : ∀ (fp : Operator → ℝ)
    (h : ∀ O : Operator, betaFunction O fp = 0) (O : Operator),
    stabilityMatrix fp O O = massDimension O + anomalousDimension O fp - d

/-- Coupling configuration in an RG framework -/
abbrev CouplingConfig {d : ℕ} (rg : RGFramework d) := rg.Operator → ℝ

/- ============= OPERATOR CLASSIFICATION ============= -/

/-- Relevant operator: Δ < d. Grows toward IR.
    These dominate low-energy physics and determine the universality class. -/
def Relevant {d : ℕ} (rg : RGFramework d) (O : rg.Operator) : Prop :=
  rg.massDimension O < d

/-- Marginal operator: Δ = d. Scale-invariant at classical level. -/
def Marginal {d : ℕ} (rg : RGFramework d) (O : rg.Operator) : Prop :=
  rg.massDimension O = d

/-- Irrelevant operator: Δ > d. Suppressed in IR by (E/Λ)^(Δ-d). -/
def Irrelevant {d : ℕ} (rg : RGFramework d) (O : rg.Operator) : Prop :=
  rg.massDimension O > d

/-- Renormalizable interaction: Δ ≤ d -/
def Renormalizable {d : ℕ} (rg : RGFramework d) (O : rg.Operator) : Prop :=
  rg.massDimension O ≤ d

/- ============= COUPLINGS ============= -/

/-- Coupling constant g_i for operator O_i. Has mass dimension [g_i] = d - [O_i]. -/
structure Coupling {d : ℕ} (rg : RGFramework d) where
  operator : rg.Operator
  value : ℝ

/-- Dimensionless coupling: g̃ = g · Λ^([O] - d) -/
noncomputable def dimensionlessCoupling {d : ℕ} (rg : RGFramework d)
    (c : Coupling rg) (Λ : Cutoff) : ℝ :=
  c.value * Λ.Λ ^ (rg.massDimension c.operator - d)

/- ============= FIXED POINTS ============= -/

/-- Fixed point: all beta functions vanish.
    At a fixed point g*, the theory is scale-invariant (a CFT). -/
def FixedPoint {d : ℕ} (rg : RGFramework d) (g : CouplingConfig rg) : Prop :=
  ∀ O : rg.Operator, rg.betaFunction O g = 0

/-- Gaussian (free) fixed point: all couplings vanish -/
def GaussianFixedPoint {d : ℕ} (rg : RGFramework d) : CouplingConfig rg := fun _ => 0

/-- The free theory is always a fixed point -/
theorem gaussian_is_fixed_point {d : ℕ} (rg : RGFramework d) :
    FixedPoint rg (GaussianFixedPoint rg) :=
  fun O => rg.gaussian_is_fixed_point O

/-- Interacting (non-Gaussian) fixed point -/
def InteractingFixedPoint {d : ℕ} (rg : RGFramework d) (g : CouplingConfig rg) : Prop :=
  FixedPoint rg g ∧ g ≠ GaussianFixedPoint rg

/- ============= SCALING DIMENSIONS ============= -/

/-- Full scaling dimension at a fixed point: Δ = Δ_classical + γ -/
noncomputable def scalingDimension {d : ℕ} (rg : RGFramework d)
    (O : rg.Operator) (fp : CouplingConfig rg) : ℝ :=
  rg.massDimension O + rg.anomalousDimension O fp

/-- At the Gaussian fixed point, anomalous dimensions vanish -/
theorem gaussian_no_anomalous {d : ℕ} (rg : RGFramework d) (O : rg.Operator) :
    rg.anomalousDimension O (GaussianFixedPoint rg) = 0 :=
  rg.gaussian_no_anomalous O

/- ============= RG FLOW ============= -/

/-- RG trajectory: a path in coupling space parametrized by scale -/
structure RGTrajectory {d : ℕ} (rg : RGFramework d) where
  /-- Coupling configuration at each scale -/
  path : Scale → CouplingConfig rg

/-- A theory flows to a fixed point in the IR -/
def FlowsToIRFixedPoint {d : ℕ} (rg : RGFramework d) (traj : RGTrajectory rg) : Prop :=
  FixedPoint rg (rg.irLimit traj.path)

/-- A theory flows from a fixed point in the UV -/
def FlowsFromUVFixedPoint {d : ℕ} (rg : RGFramework d) (traj : RGTrajectory rg) : Prop :=
  FixedPoint rg (rg.uvLimit traj.path)

/- ============= STABILITY AND CRITICAL SURFACE ============= -/

/-- Eigenvalue of stability matrix = scaling dimension - d -/
theorem stability_eigenvalue_relation {d : ℕ} (rg : RGFramework d)
    (fp : CouplingConfig rg) (h : FixedPoint rg fp) (O : rg.Operator) :
  rg.stabilityMatrix fp O O = scalingDimension rg O fp - d :=
  rg.stability_eigenvalue_relation fp h O

/-- Critical surface: the set of theories that flow to a given IR fixed point -/
structure CriticalSurface {d : ℕ} (rg : RGFramework d) where
  ir_fixed_point : CouplingConfig rg
  is_fixed : FixedPoint rg ir_fixed_point
  /-- Theories on this surface -/
  theories : Set (CouplingConfig rg)
  /-- All theories on the surface flow to the fixed point -/
  all_flow_to_fp : ∀ g ∈ theories, ∃ traj : RGTrajectory rg,
    traj.path 1 = g ∧ rg.irLimit traj.path = ir_fixed_point

end ModularPhysics.Core.QFT.RG

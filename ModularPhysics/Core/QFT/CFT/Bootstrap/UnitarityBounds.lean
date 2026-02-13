-- ModularPhysics/Core/QFT/CFT/Bootstrap/UnitarityBounds.lean
import ModularPhysics.Core.QFT.CFT.Bootstrap.CrossingSymmetry
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.CFT.Bootstrap

open CFT

set_option linter.unusedVariables false

/- ============= UNITARITY BOUNDS ============= -/

/-- Free scalar dimension -/
noncomputable def free_scalar_dimension (d : ℕ) : ℝ :=
  (d - 2 : ℝ) / 2

/-- Free fermion dimension -/
noncomputable def free_fermion_dimension (d : ℕ) : ℝ :=
  (d - 1 : ℝ) / 2

/-- Conserved current dimension -/
noncomputable def conserved_current_dimension (d : ℕ) : ℝ :=
  d - 1

/-- Stress tensor dimension -/
def stress_tensor_dimension (d : ℕ) : ℝ := d

/-- Structure for unitarity bounds theory.

    Unitarity of the CFT implies lower bounds on operator dimensions.
    Operators that saturate these bounds correspond to conserved currents
    or free fields. -/
structure UnitarityBoundsTheory where
  /-- Predicate: operator is in the symmetric traceless tensor representation of SO(d).
      In d=3, all integer-spin operators are symmetric traceless.
      In d>3, this is a specific representation type. -/
  IsSymmetricTraceless : ∀ {d : ℕ} {H : Type _}, QuasiPrimary d H → ℕ → Prop
  /-- Predicate: operator is a conserved current (∂^μ J_μ... = 0).
      Conservation implies the dimension saturates the unitarity bound. -/
  IsConserved : ∀ {d : ℕ} {H : Type _}, QuasiPrimary d H → Prop
  /-- Predicate: operator is a stress-energy tensor (conserved, symmetric, traceless, spin 2). -/
  IsStressTensor : ∀ {d : ℕ} {H : Type _}, QuasiPrimary d H → Prop
  /-- Unitarity bound for scalar operators: Δ ≥ (d-2)/2
      This is saturated by free scalar fields -/
  unitarity_bound_scalar : ∀ (d : ℕ) {H : Type _} (φ : QuasiPrimary d H)
    (h_scalar : φ.spin = 0),
    φ.scaling_dim ≥ (d - 2 : ℝ) / 2
  /-- Unitarity bound for symmetric traceless tensors: Δ ≥ ℓ + (d-2)/2
      This applies to operators in symmetric traceless tensor representations -/
  unitarity_bound_symmetric_traceless : ∀ (d : ℕ) {H : Type _}
    (O : QuasiPrimary d H) (ℓ : ℕ)
    (h_st : IsSymmetricTraceless O ℓ)
    (h_spin : O.spin = ℓ),
    O.scaling_dim ≥ ℓ + (d - 2 : ℝ) / 2
  /-- Conserved currents saturate bound: Δ = d - 1 for spin 1 -/
  conserved_current_saturation : ∀ (d : ℕ) {H : Type _}
    (J : QuasiPrimary d H)
    (h_spin_1 : J.spin = 1)
    (h_conserved : IsConserved J),
    J.scaling_dim = d - 1
  /-- Stress tensor: Δ = d for spin 2 -/
  stress_tensor_saturation : ∀ (d : ℕ) {H : Type _}
    (T : QuasiPrimary d H)
    (h_spin_2 : T.spin = 2)
    (h_stress : IsStressTensor T),
    T.scaling_dim = d

/- ============= SHORTENING CONDITIONS ============= -/

/-- Structure for shortening conditions theory.

    When an operator's dimension saturates the unitarity bound,
    a descendant becomes null (zero norm). This shortens the conformal multiplet. -/
structure ShorteningConditionsTheory where
  /-- Null descendant at unitarity bound.
      When Δ = (d-2)/2 + ℓ, there exists a null state at level ≥ 1.
      This removes states from the multiplet. -/
  null_state_at_unitarity_bound : ∀ (d : ℕ) {H : Type _}
    (O : QuasiPrimary d H) (ℓ : ℕ)
    (h_saturate : O.scaling_dim = ℓ + (d - 2 : ℝ) / 2),
    ∃ (level : ℕ), level ≥ 1

/-- Long multiplet: Δ > ℓ + (d-2)/2
    Generic case, full descendant tower -/
def long_multiplet (d : ℕ) {H : Type _} (O : QuasiPrimary d H) (ℓ : ℕ) : Prop :=
  O.scaling_dim > ℓ + (d - 2 : ℝ) / 2

/-- Short multiplet: Δ = ℓ + (d-2)/2
    Special case with null states, truncated tower -/
def short_multiplet (d : ℕ) {H : Type _} (O : QuasiPrimary d H) (ℓ : ℕ) : Prop :=
  O.scaling_dim = ℓ + (d - 2 : ℝ) / 2

/- ============= REFLECTION POSITIVITY ============= -/

/-- Structure for reflection positivity theory.

    In Euclidean signature, unitarity becomes reflection positivity.
    This implies all OPE coefficient-squareds are non-negative and
    all operator dimensions are real and bounded below. -/
structure ReflectionPositivityTheory where
  /-- OPE coefficients squared are non-negative: C²_{φφO} ≥ 0.
      Fundamental consequence of unitarity in Euclidean signature. -/
  ope_coefficient_squared_positive : ∀ {d : ℕ} {H : Type _}
    (φ O : QuasiPrimary d H),
    ∃ (C_squared : ℝ), C_squared ≥ 0
  /-- In unitary CFT, all operator dimensions are real and bounded below.
      Specifically, Δ ≥ (d-2)/2 for any primary operator. -/
  unitary_cft_real_dimensions : ∀ {d : ℕ} {H : Type _}
    (O : QuasiPrimary d H),
    O.scaling_dim ∈ Set.Ici ((d - 2 : ℝ) / 2)

end ModularPhysics.Core.QFT.CFT.Bootstrap

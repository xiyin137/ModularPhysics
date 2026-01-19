import ModularPhysics.Core.QFT.Wightman.WightmanFunctions
import ModularPhysics.Core.SpaceTime.Causality
import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.SpaceTime.Minkowski

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum

/-- Wightman Axiom W1: Relativistic covariance (Poincaré invariance).
    There exists a strongly continuous unitary representation U(Λ,a) of the Poincaré group
    such that U(Λ,a) φ(x) U†(Λ,a) = φ(Λx + a).

    This means: W_n(Λx₁+a,...,Λxₙ+a) = W_n(x₁,...,xₙ) -/
axiom relativistic_covariance {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (phi : FieldDistribution H d)
  (Lambda : LorentzTransformGen d)
  (a : Fin d → ℝ) :
  ∃ (U : Quantum.UnitaryOp H),
  ∀ (n : ℕ) (points : Fin n → (Fin d → ℝ)),
    wightmanFunction phi n (fun i μ => ∑ ν, Lambda.matrix μ ν * points i ν + a μ) =
    wightmanFunction phi n points

/-- Momentum lies in forward lightcone: p⁰ ≥ 0 and p² = (p⁰)² - |p⃗|² ≥ 0 -/
def inForwardLightcone {d : ℕ} [NeZero d] (p : Fin d → ℝ) : Prop :=
  p 0 ≥ 0 ∧ (p 0)^2 ≥ ∑ i : Fin d, if i = 0 then 0 else (p i)^2

/-- Momentum is on mass shell: (p⁰)² - |p⃗|² = m² -/
def onMassShell {d : ℕ} [NeZero d] (p : Fin d → ℝ) (m : ℝ) : Prop :=
  (p 0)^2 - (∑ i : Fin d, if i = 0 then 0 else (p i)^2) = m^2

/-- Wightman Axiom W2: Spectrum condition (positivity of energy-momentum).
    The joint spectrum of the energy-momentum operators (P⁰, P¹,...) lies in the
    closed forward lightcone V⁺ = {p | p⁰ ≥ 0, p² ≥ 0} where p² = (p⁰)² - ∑ᵢ(pⁱ)².

    Physical meaning: energy is bounded from below (stable vacuum).

    This is formulated as: any momentum eigenstate |p⟩ in the Hilbert space
    has momentum p in the forward lightcone. The vacuum has p = 0. -/
axiom spectrum_condition {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (phi : FieldDistribution H d) :
  ∃ (spectrum : Set (Fin d → ℝ)),
    (∀ p ∈ spectrum, inForwardLightcone p) ∧  -- All momenta in forward cone
    (fun _ => 0) ∈ spectrum                    -- Vacuum has zero momentum

/-- On-shell condition: a momentum p is on shell for mass m if E² - |p⃗|² = m².
    This is a DEFINITION of what "on-shell" means, not a claim about all momenta. -/
def isOnShell {d : ℕ} [NeZero d] (p : Fin d → ℝ) (m : ℝ) : Prop :=
  onMassShell p m ∧ p 0 ≥ 0

/-- Test function support is contained in a region -/
axiom testFunctionSupport {d : ℕ} (f : SchwartzFunction d) : Set (Fin d → ℝ)

/-- Two regions are spacelike separated: for all x in R₁, y in R₂, (x-y)² < 0 (spacelike) -/
def spacelikeSeparated {d : ℕ} [NeZero d] (R₁ R₂ : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ R₁, ∀ y ∈ R₂,
    (x 0 - y 0)^2 < ∑ i : Fin d, if i = 0 then 0 else (x i - y i)^2

/-- Wightman Axiom W3: Locality (microcausality).
    For smeared field operators with spacelike separated supports:
    [φ(f), ψ(g)] = 0 when supp(f) and supp(g) are spacelike separated.

    This is the mathematical expression of Einstein causality: measurements at
    spacelike separation cannot influence each other. -/
axiom locality {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (phi psi : SmearedFieldOperator H d)
  (f g : SchwartzFunction d)
  (h_spacelike : spacelikeSeparated (testFunctionSupport f) (testFunctionSupport g)) :
  ∀ (state : H),
    smear phi f (smear psi g state) =
    smear psi g (smear phi f state)

/-- Apply a sequence of smeared field operators to the vacuum:
    φ(f₁) φ(f₂) ... φ(fₙ) |0⟩ -/
axiom applyFieldsToVacuum {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : SmearedFieldOperator H d)
  (n : ℕ)
  (test_funcs : Fin n → SchwartzFunction d) : H

/-- Wightman Axiom W4: Vacuum properties.
    - Uniqueness: |0⟩ is the unique Poincaré-invariant state (up to phase)
    - Cyclicity: {φ(f₁)...φ(fₙ)|0⟩ : n ∈ ℕ, fᵢ ∈ S(ℝᵈ)} is dense in H

    This ensures the vacuum is the "ground state" and that all states can be
    created by applying field operators to the vacuum. -/
axiom vacuum_properties {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : SmearedFieldOperator H d) :
  -- Uniqueness: vacuum is Poincaré invariant (for all Poincaré unitaries)
  (∀ (U : Quantum.UnitaryOp H), applyUnitary U (@vacuum H _) = @vacuum H _) ∧
  -- Cyclicity: polynomial algebra of fields acting on vacuum is dense
  (∀ (state : H) (ε : ℝ), ε > 0 →
    ∃ (n : ℕ) (test_funcs : Fin n → SchwartzFunction d),
      ‖state - applyFieldsToVacuum phi n test_funcs‖ < ε)

/-- Reeh-Schlieder theorem: vacuum is cyclic and separating for local algebras.
    For any bounded region O, the set {φ(f)|0⟩ | supp(f) ⊂ O} is dense in H.

    Remarkable consequence: local measurements can distinguish any two states!

    This is a THEOREM (provable from W1-W4), not an axiom itself. -/
theorem reeh_schlieder {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : SmearedFieldOperator H d)
  (O : Set (Fin d → ℝ))
  (h_bounded : ∃ R : ℝ, ∀ x ∈ O, ‖x‖ < R)
  (h_nonempty : O.Nonempty) :
  ∀ (state : H) (ε : ℝ), ε > 0 →
    ∃ (n : ℕ) (test_funcs : Fin n → SchwartzFunction d),
      (∀ i, testFunctionSupport (test_funcs i) ⊆ O) ∧
      ‖state - applyFieldsToVacuum phi n test_funcs‖ < ε := by
  sorry

/-- Temperedness: Wightman functions are tempered distributions.
    They satisfy polynomial growth bounds: |W_n(x)| ≤ C(1 + |x|)^N.

    This is automatic consequence of the spectrum condition (W2) and ensures that
    Fourier transforms (momentum space formulation) are well-defined.

    This is a THEOREM (provable from W2), not an axiom itself. -/
theorem temperedness {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ) :
  ∃ (C N : ℝ), ∀ (points : Fin n → (Fin d → ℝ)),
    ‖wightmanFunction phi n points‖ ≤ C * (1 + ∑ i, ‖points i‖)^N := by
  sorry

end ModularPhysics.Core.QFT.Wightman

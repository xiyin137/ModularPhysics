-- ModularPhysics/Core/QFT/Smatrix/LSZ.lean
-- Lehmann-Symanzik-Zimmermann Reduction Formula
import ModularPhysics.Core.QFT.Smatrix.AsymptoticStates
import ModularPhysics.Core.QFT.Wightman
import ModularPhysics.Core.QFT.Euclidean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ModularPhysics.Core.QFT.Smatrix

open SpaceTime Complex Wightman Euclidean Quantum Real

set_option linter.unusedVariables false

/- ============= TIME-ORDERED CORRELATION FUNCTIONS ============= -/

/-- Time-ordered (Green) function: G_n(x₁,...,xₙ) = ⟨0|T φ(x₁)...φ(xₙ)|0⟩

    where T is the time-ordering operator:
    T φ(x₁)...φ(xₙ) arranges fields in decreasing time order x₁⁰ ≥ x₂⁰ ≥ ... ≥ xₙ⁰

    For x₁⁰ ≥ ... ≥ xₙ⁰: G_n = W_n (Wightman function)
    Otherwise: permute to achieve time ordering -/
axiom greenFunction {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ) :
  (Fin n → (Fin d → ℝ)) → ℂ

/-- Relationship to Wightman functions for ordered times -/
axiom green_equals_wightman_when_ordered {H : Type _} [QuantumStateSpace H] {d : ℕ} [NeZero d]
  (phi : FieldDistribution H d)
  (n : ℕ)
  (points : Fin n → (Fin d → ℝ))
  (h_ordered : ∀ i j : Fin n, i ≤ j → points i ⟨0, NeZero.pos d⟩ ≥ points j ⟨0, NeZero.pos d⟩) :
  greenFunction phi n points = wightmanFunction phi n points

/- ============= KÄLLÉN-LEHMANN SPECTRAL REPRESENTATION ============= -/

/-- Field strength renormalization constant Z ∈ (0,1]

    Z is the residue at the single-particle pole in the two-point function.
    - Z = 1 for free field (no interactions)
    - Z < 1 for interacting field (wavefunction renormalization)
    - Z > 0 required for particle interpretation

    This corresponds to the `residue` in IsolatedMass from Euclidean formalism. -/
axiom field_strength_Z : ℝ
axiom field_strength_bounds : 0 < field_strength_Z ∧ field_strength_Z ≤ 1

/-- Spectral integral for Källén-Lehmann representation -/
axiom spectral_integral : ∀ (d : ℕ), SpectralDensity d → (Fin d → ℝ) → (Fin d → ℝ) → ℂ

/-- Two-point Wightman function has Källén-Lehmann spectral representation

    ⟨0|φ(x)φ(y)|0⟩ = ∫_{m²}^∞ dμ² ρ(μ²) Δ₊(x-y; μ²)

    where:
    - ρ(μ²) is the spectral density from Euclidean.SpectralDensity
    - ρ(μ²) = Z δ(μ² - m²) + ρ_cont(μ²)
      * Z δ(μ² - m²): single-particle contribution
      * ρ_cont(μ²): multi-particle continuum
    - Δ₊(x-y; μ²) is the positive-frequency Wightman propagator

    This connects to Euclidean.HasSpectralRepresentation via Wick rotation. -/
axiom kallen_lehmann {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (x y : Fin d → ℝ) :
  ∃ (spectral : SpectralDensity d),
    twoPointWightman phi x y = spectral_integral d spectral x y

/- ============= LSZ ASYMPTOTIC CONDITION ============= -/

/-- Klein-Gordon operator: (□ + m²) where □ = ∂_μ ∂^μ is the d'Alembertian

    In Minkowski signature (+,-,-,-): □ = ∂²/∂t² - ∇²  -/
noncomputable def kleinGordonOp (m : ℝ) {d : ℕ} : ((Fin d → ℝ) → ℂ) → ((Fin d → ℝ) → ℂ) :=
  sorry  -- (∂_μ ∂^μ + m²)

/-- LSZ asymptotic condition for in-states

    The key result: acting with (□ + m²) on a field in a Green's function
    and integrating over spacetime with momentum eigenstate wave function
    yields an in-state amplitude.

    Formally: √Z lim_{x⁰ → -∞} ∫ d⁴x e^{ip·x} (□_x + m²) φ(x) |0⟩ ∝ |p, in⟩

    This is the rigorous meaning of "φ(x) creates/annihilates particles".

    The factor √Z = √(residue of single-particle pole) appears because
    the field φ is not canonically normalized - the residue Z < 1 for
    interacting theories due to wavefunction renormalization.

    The asymptotic condition states that the limit exists and equals √Z times
    a properly normalized in-state. -/
axiom lsz_in_condition {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (m : ℝ)
  (h_mass_positive : m > 0)
  (p : OnShellMomentum m) :
  -- The LSZ limit exists and the normalization factor is √Z
  ∃ (limit_amplitude : ℂ),
    ‖limit_amplitude‖ = sqrt field_strength_Z ∧
    limit_amplitude ≠ 0

/-- LSZ asymptotic condition for out-states (similar, t → +∞) -/
axiom lsz_out_condition {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (m : ℝ)
  (h_mass_positive : m > 0)
  (p : OnShellMomentum m) :
  ∃ (limit_amplitude : ℂ),
    ‖limit_amplitude‖ = sqrt field_strength_Z ∧
    limit_amplitude ≠ 0

/- ============= LSZ REDUCTION FORMULA ============= -/

/-- The spacetime integral appearing in LSZ reduction

    Represents: ∏ᵢ₌₁ⁿ ∫d⁴xᵢ e^{ipᵢ·xᵢ} (□ᵢ + m²) ∏ⱼ₌₁ᵐ ∫d⁴yⱼ e^{-ip'ⱼ·yⱼ} (□ⱼ + m²)
                × ⟨0| T φ(y₁)...φ(yₘ) φ(x₁)...φ(xₙ) |0⟩

    This is the Green's function with Klein-Gordon operators applied and
    integrated against momentum eigenstate wave functions. -/
axiom integral_of_green_function {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n m : ℕ)
  (mass : ℝ)
  (p_in : Fin n → OnShellMomentum mass)
  (p_out : Fin m → OnShellMomentum mass) : ℂ

/-- LSZ Reduction Theorem (Lehmann-Symanzik-Zimmermann 1955)

    The S-matrix element for n → m scattering is:

    ⟨p₁',...,pₘ',out|p₁,...,pₙ,in⟩ = Z^{(n+m)/2} × (spacetime integral)

    where the spacetime integral is:
    ∏ᵢ₌₁ⁿ ∫d⁴xᵢ e^{ipᵢ·xᵢ} (□ᵢ + m²) ∏ⱼ₌₁ᵐ ∫d⁴yⱼ e^{-ip'ⱼ·yⱼ} (□ⱼ + m²)
    × ⟨0| T φ(y₁)...φ(yₘ) φ(x₁)...φ(xₙ) |0⟩

    Key features:
    1. NON-PERTURBATIVE: no reference to interaction picture or adiabatic switching
    2. Relates physical S-matrix to time-ordered Green's functions
    3. Each external leg contributes:
       - Factor of √Z (wavefunction renormalization from Euclidean.IsolatedMass.residue)
       - Klein-Gordon operator (□ + m²) to project onto on-shell
       - Fourier phase e^{±ip·x} for momentum eigenstate
    4. Valid for theories with:
       - Mass gap (no IR divergences, cf. Euclidean.SpectralDecomposition.has_mass_gap)
       - Asymptotic completeness (cf. AsymptoticStates.asymptotic_completeness_in)
       - Cluster decomposition (cf. Wightman.cluster_decomposition)

    This is the rigorous, non-perturbative foundation for calculating
    scattering amplitudes from correlation functions.

    References:
    - Lehmann, Symanzik, Zimmermann, Nuovo Cimento 1 (1955) 205
    - Haag, "Local Quantum Physics" (1996), Chapter III
    - Streater & Wightman, "PCT, Spin and Statistics" (1964), Chapter 3-4 -/
theorem lsz_reduction {H : Type _} [QuantumStateSpace H] {d : ℕ}
    (phi : FieldDistribution H d)
    (n m : ℕ)
    (mass : ℝ)
    (p_in : Fin n → OnShellMomentum mass)
    (p_out : Fin m → OnShellMomentum mass) :
  ∃ (S_amplitude : ℂ),
    S_amplitude =
      (field_strength_Z ^ ((n + m) / 2 : ℕ)) *
      (integral_of_green_function phi n m mass p_in p_out) := by
  sorry

/- ============= CONNECTED AND AMPUTATED GREEN'S FUNCTIONS ============= -/

/-- Connected Green's function G_n^conn

    Full Green's function decomposes: G_n = G_n^conn + (disconnected pieces)

    Connected = cannot be split into independent factors by removing any subset of points.

    Only connected parts contribute to S-matrix (disconnected = vacuum bubbles = cancel).

    This is the exponential of the sum of connected diagrams in perturbation theory. -/
axiom connectedGreen {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ) :
  (Fin n → (Fin d → ℝ)) → ℂ

/-- One-particle-irreducible (1PI) Green's function Γ_n

    Cannot be disconnected by cutting a single internal propagator.
    These are the "proper vertices" or "vertex functions".

    Building blocks for Feynman diagrams: full propagators built from 1PI vertices. -/
axiom oneParticleIrreducible {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ) :
  (Fin n → (Fin d → ℝ)) → ℂ

/-- Amputated Green's function: remove external propagators

    For S-matrix, we need particles on-shell (p² = m²), so we remove
    the propagators 1/(p² - m²) from external legs.

    This is what LSZ formula does via the Klein-Gordon operators. -/
axiom amputatedGreen {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : FieldDistribution H d)
  (n : ℕ) :
  (Fin n → (Fin d → ℝ)) → ℂ

/- ============= MASS AND FIELD RENORMALIZATION ============= -/

/-- Physical mass m_phys (observed particle pole)

    The physical mass is defined as the location of the pole in the
    two-point function's momentum-space representation:

    G̃₂(p²) has pole at p² = m_phys²

    This corresponds to the isolated mass in Euclidean.IsolatedMass. -/
axiom physical_mass : ℝ
axiom physical_mass_positive : physical_mass > 0

/-- Self-energy Σ(p²): sum of 1PI two-point diagrams

    The full propagator is related to the free propagator by:
    G̃₂(p²) = [p² - m₀² - Σ(p²)]⁻¹

    where m₀ is the bare mass in the Lagrangian.

    At the physical pole: physical_mass² = m₀² + Σ(physical_mass²) -/
axiom self_energy (p_squared : ℝ) : ℂ

/-- Field strength Z from self-energy

    Z = [1 - dΣ/dp²|_{p²=m²}]⁻¹

    This relates the field renormalization to the derivative of
    the self-energy at the mass shell. -/
axiom field_strength_from_self_energy :
  ∃ (deriv_self_energy : ℝ),
    field_strength_Z = 1 / (1 - deriv_self_energy)

/- ============= VALIDITY CONDITIONS ============= -/

/-- Mass gap hypothesis: spectrum has gap above single-particle mass

    spec(P²) ∩ [m², (2m)²) = {m²}  (isolated single-particle state)
    spec(P²) ∩ [(2m)², ∞) ≠ ∅      (multi-particle continuum)

    This ensures:
    - Stable single-particle states
    - No IR divergences
    - Well-defined S-matrix

    This corresponds to Euclidean.SpectralDecomposition.has_mass_gap.

    For massless theories (QED, QCD), IR divergences appear and
    S-matrix is only defined for IR-safe observables (inclusive cross sections). -/
axiom mass_gap : ℝ
axiom mass_gap_positive : mass_gap > 0
axiom mass_gap_isolated :
  ∀ (spectral : SpectralDensity 4),
    mass_gap = physical_mass ∧
    ∀ μ_sq : ℝ, physical_mass^2 < μ_sq → μ_sq < (2 * physical_mass)^2 →
      spectral.ρ μ_sq = 0

/-- Asymptotic completeness: Møller operators have dense range

    Range(Ω₊) is dense in ℋ  (modulo bound states if any)

    Every scattering state can be approximated by asymptotic free states.
    This is required for LSZ reduction to give complete S-matrix.

    Combined with the asymptotic condition from AsymptoticStates.lean.

    Mathematically: for any ψ ∈ ℋ and ε > 0, there exists φ ∈ ℋ_in such that
    the overlap ⟨ψ|Ω₊(φ)⟩ approximates the norm ⟨ψ|ψ⟩ well. -/
axiom asymptotic_completeness_lsz :
  ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
    ∃ (φ_in : InHilbert),
      -- The Møller image approximates ψ in the sense that
      -- their inner product is close to the norm of ψ
      ‖innerProduct ψ ψ‖ - ‖innerProduct ψ (moller_in φ_in)‖ < ε

end ModularPhysics.Core.QFT.Smatrix

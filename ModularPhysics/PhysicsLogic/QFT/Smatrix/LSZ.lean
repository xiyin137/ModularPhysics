-- ModularPhysics/Core/QFT/Smatrix/LSZ.lean
-- Lehmann-Symanzik-Zimmermann Reduction Formula
import ModularPhysics.PhysicsLogic.QFT.Smatrix.AsymptoticStates
import ModularPhysics.PhysicsLogic.QFT.Wightman
import ModularPhysics.PhysicsLogic.QFT.Euclidean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ModularPhysics.Core.QFT.Smatrix

open SpaceTime Complex Euclidean Real

set_option linter.unusedVariables false

/-!
# Lehmann-Symanzik-Zimmermann (LSZ) Reduction Formula

The LSZ reduction formula relates S-matrix elements to time-ordered
Green's functions. It is the bridge between correlation functions
(computable via Feynman diagrams) and scattering amplitudes (observable).

## Key concepts:

1. **Time-ordered Green's functions**: G_n(x₁,...,xₙ) = ⟨0|T φ(x₁)...φ(xₙ)|0⟩
2. **Källén-Lehmann spectral representation**: decomposes 2-point function
   into single-particle and multi-particle contributions
3. **Field strength renormalization Z**: residue at single-particle pole
4. **LSZ reduction**: S-matrix = Z^{(n+m)/2} × (Klein-Gordon applied Green's function)

## References:
- Lehmann, Symanzik, Zimmermann, Nuovo Cimento 1 (1955) 205
- Haag, "Local Quantum Physics" (1996), Chapter III
- Streater & Wightman, "PCT, Spin and Statistics" (1964), Chapter 3-4
-/

/- ============= KLEIN-GORDON OPERATOR ============= -/

/-- Klein-Gordon operator: (□ + m²) where □ = ∂_μ ∂^μ is the d'Alembertian

    In Minkowski signature (+,-,-,-): □ = ∂²/∂t² - ∇² -/
noncomputable def kleinGordonOp (m : ℝ) {d : ℕ} : ((Fin d → ℝ) → ℂ) → ((Fin d → ℝ) → ℂ) :=
  sorry  -- (∂_μ ∂^μ + m²)

/- ============= LSZ DATA ============= -/

/-- LSZ reduction framework data.

    Bundles all the data needed for the LSZ reduction formula:
    - Time-ordered and Wightman n-point functions
    - Connected, 1PI, and amputated Green's functions
    - Källén-Lehmann spectral representation
    - Field strength renormalization and physical mass
    - LSZ asymptotic conditions
    - The spacetime integral appearing in the reduction formula

    Parameterized by spacetime dimension `d` (must be ≥ 1 for time direction). -/
structure LSZData (d : ℕ) [NeZero d] where
  /- === Correlation functions === -/

  /-- n-point Wightman function W_n(x₁,...,xₙ) = ⟨0|φ(x₁)...φ(xₙ)|0⟩

      Operator-ordered (NOT time-ordered). -/
  wightmanFunction : (n : ℕ) → (Fin n → (Fin d → ℝ)) → ℂ
  /-- Time-ordered (Green) function G_n(x₁,...,xₙ) = ⟨0|T φ(x₁)...φ(xₙ)|0⟩

      T arranges fields in decreasing time order. -/
  greenFunction : (n : ℕ) → (Fin n → (Fin d → ℝ)) → ℂ
  /-- Green = Wightman when times are already ordered -/
  green_equals_wightman_when_ordered : ∀ (n : ℕ) (points : Fin n → (Fin d → ℝ))
    (_ : ∀ i j : Fin n, i ≤ j → points i ⟨0, NeZero.pos d⟩ ≥ points j ⟨0, NeZero.pos d⟩),
    greenFunction n points = wightmanFunction n points

  /-- Connected Green's function G_n^conn

      Full Green's function decomposes: G_n = G_n^conn + (disconnected pieces).
      Only connected parts contribute to S-matrix. -/
  connectedGreen : (n : ℕ) → (Fin n → (Fin d → ℝ)) → ℂ
  /-- One-particle-irreducible (1PI) Green's function Γ_n

      Cannot be disconnected by cutting a single internal propagator.
      These are the "proper vertices" — building blocks for Feynman diagrams. -/
  oneParticleIrreducible : (n : ℕ) → (Fin n → (Fin d → ℝ)) → ℂ
  /-- Amputated Green's function: external propagators removed.

      For S-matrix, we need on-shell particles (p² = m²), so we remove
      propagators 1/(p² - m²) from external legs. -/
  amputatedGreen : (n : ℕ) → (Fin n → (Fin d → ℝ)) → ℂ

  /- === Field strength and physical mass === -/

  /-- Field strength renormalization constant Z ∈ (0,1]

      Z is the residue at the single-particle pole in the two-point function.
      - Z = 1 for free field (no interactions)
      - Z < 1 for interacting field (wavefunction renormalization)
      - Z > 0 required for particle interpretation -/
  field_strength_Z : ℝ
  field_strength_bounds : 0 < field_strength_Z ∧ field_strength_Z ≤ 1

  /-- Physical mass m_phys (location of pole in two-point function):
      G̃₂(p²) has pole at p² = m_phys² -/
  physical_mass : ℝ
  physical_mass_positive : physical_mass > 0

  /-- Self-energy Σ(p²): sum of 1PI two-point diagrams.

      Full propagator: G̃₂(p²) = [p² - m₀² - Σ(p²)]⁻¹
      Physical pole: physical_mass² = m₀² + Σ(physical_mass²) -/
  self_energy : ℝ → ℂ

  /-- Z = [1 - dΣ/dp²|_{p²=m²}]⁻¹ -/
  field_strength_from_self_energy :
    ∃ (deriv_self_energy : ℝ),
      field_strength_Z = 1 / (1 - deriv_self_energy)

  /- === Spectral representation === -/

  /-- Spectral integral for Källén-Lehmann representation -/
  spectral_integral : SpectralDensity d → (Fin d → ℝ) → (Fin d → ℝ) → ℂ

  /-- Källén-Lehmann spectral representation for the two-point function

      W₂(x,y) = ∫_{m²}^∞ dμ² ρ(μ²) Δ₊(x-y; μ²)

      where ρ(μ²) = Z δ(μ² - m²) + ρ_cont(μ²):
      - Z δ(μ² - m²): single-particle contribution
      - ρ_cont(μ²): multi-particle continuum -/
  kallen_lehmann : ∀ (x y : Fin d → ℝ),
    ∃ (spectral : SpectralDensity d),
      wightmanFunction 2 (fun i => if i = 0 then x else y) =
        spectral_integral spectral x y

  /- === LSZ asymptotic conditions === -/

  /-- LSZ asymptotic condition (in): acting with (□ + m²) on a field
      in a Green's function and integrating against momentum eigenstates
      yields an in-state amplitude.

      √Z lim_{x⁰ → -∞} ∫ d⁴x e^{ip·x} (□_x + m²) φ(x) |0⟩ ∝ |p, in⟩ -/
  lsz_in_condition : ∀ (m : ℝ) (_ : m > 0) (p : OnShellMomentum m),
    ∃ (limit_amplitude : ℂ),
      ‖limit_amplitude‖ = sqrt field_strength_Z ∧
      limit_amplitude ≠ 0
  /-- LSZ asymptotic condition (out): similar, t → +∞ -/
  lsz_out_condition : ∀ (m : ℝ) (_ : m > 0) (p : OnShellMomentum m),
    ∃ (limit_amplitude : ℂ),
      ‖limit_amplitude‖ = sqrt field_strength_Z ∧
      limit_amplitude ≠ 0

  /- === LSZ integral === -/

  /-- The spacetime integral appearing in LSZ reduction:

      ∏ᵢ ∫d⁴xᵢ e^{ipᵢ·xᵢ} (□ᵢ + m²) ∏ⱼ ∫d⁴yⱼ e^{-ip'ⱼ·yⱼ} (□ⱼ + m²)
      × ⟨0| T φ(y₁)...φ(yₘ) φ(x₁)...φ(xₙ) |0⟩ -/
  integral_of_green_function : (n m : ℕ) → (mass : ℝ) →
    (Fin n → OnShellMomentum mass) → (Fin m → OnShellMomentum mass) → ℂ

/- ============= LSZ REDUCTION THEOREM ============= -/

/-- LSZ Reduction Theorem (Lehmann-Symanzik-Zimmermann 1955)

    The S-matrix element for n → m scattering is:
    ⟨p₁',...,pₘ',out|p₁,...,pₙ,in⟩ = Z^{(n+m)/2} × (spacetime integral)

    Key features:
    1. NON-PERTURBATIVE: no reference to interaction picture
    2. Relates physical S-matrix to time-ordered Green's functions
    3. Each external leg contributes √Z, Klein-Gordon operator, Fourier phase
    4. Valid for theories with mass gap, asymptotic completeness, cluster decomposition -/
theorem lsz_reduction {d : ℕ} [NeZero d]
    (lsz : LSZData d)
    (n m : ℕ)
    (mass : ℝ)
    (p_in : Fin n → OnShellMomentum mass)
    (p_out : Fin m → OnShellMomentum mass) :
  ∃ (S_amplitude : ℂ),
    S_amplitude =
      (lsz.field_strength_Z ^ ((n + m) / 2 : ℕ)) *
      (lsz.integral_of_green_function n m mass p_in p_out) := by
  sorry

/- ============= VALIDITY CONDITIONS ============= -/

/-- Validity conditions for the LSZ reduction formula.

    Takes both the LSZ data and a scattering theory (for asymptotic completeness). -/
structure LSZValidityData {d : ℕ} [NeZero d] (lsz : LSZData d) (st : ScatteringTheoryData) where
  /-- Mass gap is isolated: spectrum has gap above single-particle mass.

      spec(P²) ∩ [m², (2m)²) = {m²}  (isolated single-particle state)
      spec(P²) ∩ [(2m)², ∞) ≠ ∅      (multi-particle continuum)

      Ensures stable single-particle states and well-defined S-matrix.
      For massless theories (QED, QCD), IR divergences appear and S-matrix
      is only defined for IR-safe observables. -/
  mass_gap_isolated :
    ∀ (spectral : SpectralDensity d),
      ∀ μ_sq : ℝ, lsz.physical_mass^2 < μ_sq →
        μ_sq < (2 * lsz.physical_mass)^2 →
        spectral.ρ μ_sq = 0
  /-- Asymptotic completeness: Møller operators have dense range.

      Range(Ω₊) is dense in ℋ (modulo bound states).
      Every scattering state can be approximated by asymptotic free states.
      Required for LSZ reduction to give the complete S-matrix. -/
  asymptotic_completeness :
    ∀ (ψ : st.H) (ε : ℝ), ε > 0 →
      ∃ (φ_in : st.InH),
        ‖st.innerProduct ψ ψ‖ - ‖st.innerProduct ψ (st.moller_in φ_in)‖ < ε

end ModularPhysics.Core.QFT.Smatrix

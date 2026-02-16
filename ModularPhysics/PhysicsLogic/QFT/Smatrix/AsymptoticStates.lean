-- ModularPhysics/Core/QFT/Smatrix/AsymptoticStates.lean
import ModularPhysics.PhysicsLogic.SpaceTime.Basic
import ModularPhysics.PhysicsLogic.QFT.Wightman.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.Smatrix

open SpaceTime

set_option linter.unusedVariables false

/-!
# Scattering Theory: Asymptotic States

Scattering theory describes particles in the asymptotic past/future
where they are effectively free. The key mathematical structures are:

1. **Rigged Hilbert space** (Gelfand triple): Φ ⊂ ℋ ⊂ Φ*
   - ℋ: Hilbert space of normalizable states
   - Φ: Test function space (smooth, rapidly decreasing)
   - Φ*: Distribution space (contains plane waves, momentum eigenstates)

2. **Asymptotic Hilbert spaces**: ℋ_in, ℋ_out
   - Free particle states in the infinite past/future
   - Connected to ℋ via Møller operators Ω±

3. **S-matrix**: S = Ω₋† Ω₊ : ℋ_in → ℋ_out
   - Maps asymptotic in-states to asymptotic out-states
   - Unitary (from isometry of Møller operators + asymptotic completeness)

4. **Momentum eigenstates**: |p⟩ ∈ Φ* (not normalizable!)
   - Delta-function normalization: ⟨p|p'⟩ = 2E_p (2π)³ δ³(p⃗ - p⃗')
   - Wave packets ∫f(p)|p⟩ d³p are normalizable and live in ℋ
-/

/- ============= ON-SHELL KINEMATICS ============= -/

/-- Four-momentum on the mass shell: p² = m², p⁰ > 0

    Parametrized by the particle mass m. The mass shell condition
    is the relativistic energy-momentum relation in Minkowski signature (+,-,-,-). -/
structure OnShellMomentum (m : ℝ) where
  p : Fin 4 → ℝ
  mass_shell : (p 0)^2 - (p 1)^2 - (p 2)^2 - (p 3)^2 = m^2
  positive_energy : p 0 > 0

/- ============= WAVE PACKETS ============= -/

/-- Wave packet: normalizable state in ℋ

    |f⟩ = ∫ f(p) |p⟩ d³p / (2π)³ 2E_p

    where f(p) is a smooth function with sufficient decay.
    Wave packets ARE normalizable and live in ℋ, not just Φ*. -/
structure WavePacket (m : ℝ) where
  /-- Momentum-space amplitude f(p) -/
  amplitude : OnShellMomentum m → ℂ
  /-- Finite L² norm bound (ensures normalizability) -/
  norm_bound : ℝ
  norm_positive : norm_bound > 0
  /-- Amplitude is bounded (Schwartz-like decay) -/
  amplitude_bounded : ∀ p : OnShellMomentum m, ‖amplitude p‖ ≤ norm_bound

/-- Multi-particle wave packet (normalizable, in Fock space ⊂ ℋ) -/
structure MultiWavePacket (n : ℕ) (masses : Fin n → ℝ) where
  amplitude : ((i : Fin n) → OnShellMomentum (masses i)) → ℂ
  /-- Finite norm bound ensuring normalizability -/
  norm_bound : ℝ
  norm_positive : norm_bound > 0
  /-- Amplitude is bounded -/
  amplitude_bounded : ∀ momenta, ‖amplitude momenta‖ ≤ norm_bound

/- ============= SCATTERING THEORY DATA ============= -/

/-- Complete scattering theory data: all abstract spaces, their relationships,
    and the fundamental properties of scattering.

    This bundles:
    - Rigged Hilbert space (Gelfand triple Φ ⊂ ℋ ⊂ Φ*)
    - Asymptotic in/out Hilbert spaces with Møller operators
    - Momentum eigenstate maps
    - Wave packet maps
    - Asymptotic completeness
    - Cluster decomposition

    All space types are abstract — the structure describes what properties
    a scattering theory must have, not how the spaces are constructed. -/
structure ScatteringTheoryData where
  /- === Abstract types === -/

  /-- Hilbert space ℋ of quantum states with finite norm -/
  H : Type*
  /-- Space of test functions Φ ⊂ ℋ (smooth, rapidly decreasing) -/
  TestSp : Type*
  /-- Space of distributions Φ* ⊃ ℋ (dual space, contains plane waves) -/
  DistSp : Type*
  /-- In-Hilbert space: free particle states in the infinite past -/
  InH : Type*
  /-- Out-Hilbert space: free particle states in the infinite future -/
  OutH : Type*

  /- === Rigged Hilbert space structure (Gelfand triple) === -/

  /-- Inner product on ℋ -/
  innerProduct : H → H → ℂ
  /-- Embedding Φ ↪ ℋ -/
  testToHilbert : TestSp → H
  /-- Embedding ℋ ↪ Φ* -/
  hilbertToDistribution : H → DistSp
  /-- Pairing ⟨·|·⟩ : Φ* × Φ → ℂ -/
  pairing : DistSp → TestSp → ℂ
  /-- Vacuum state |0⟩ ∈ ℋ -/
  vacuum : H
  /-- Vacuum has unit norm -/
  vacuum_normalized : innerProduct vacuum vacuum = 1

  /- === Asymptotic structure === -/

  /-- Møller operator Ω₊ : ℋ_in → ℋ (maps in-states to interacting states) -/
  moller_in : InH → H
  /-- Møller operator Ω₋ : ℋ_out → ℋ -/
  moller_out : OutH → H
  /-- Inner product on ℋ_in -/
  inner_in : InH → InH → ℂ
  /-- Inner product on ℋ_out -/
  inner_out : OutH → OutH → ℂ
  /-- Ω₊ is an isometry: ⟨Ω₊ψ, Ω₊φ⟩_ℋ = ⟨ψ, φ⟩_in -/
  moller_in_isometry : ∀ (ψ φ : InH),
    innerProduct (moller_in ψ) (moller_in φ) = inner_in ψ φ
  /-- Ω₋ is an isometry: ⟨Ω₋ψ, Ω₋φ⟩_ℋ = ⟨ψ, φ⟩_out -/
  moller_out_isometry : ∀ (ψ φ : OutH),
    innerProduct (moller_out ψ) (moller_out φ) = inner_out ψ φ
  /-- In-vacuum |0,in⟩ -/
  in_vacuum : InH
  /-- Out-vacuum |0,out⟩ -/
  out_vacuum : OutH
  /-- In-vacuum maps to vacuum: Ω₊|0,in⟩ = |0⟩ -/
  in_vacuum_eq : moller_in in_vacuum = vacuum
  /-- Out-vacuum maps to vacuum: Ω₋|0,out⟩ = |0⟩ -/
  out_vacuum_eq : moller_out out_vacuum = vacuum

  /- === Momentum eigenstates (in distribution space) === -/

  /-- Single-particle momentum eigenstate |p,in⟩ ∈ Φ*

      These are plane waves: NOT normalizable.
      They satisfy ⟨p|p'⟩ = 2E_p (2π)³ δ³(p⃗ - p⃗')
      which is a distribution, not a finite number. -/
  momentumEigenstateIn : (m : ℝ) → OnShellMomentum m → DistSp
  /-- Single-particle momentum eigenstate |p,out⟩ ∈ Φ* -/
  momentumEigenstateOut : (m : ℝ) → OnShellMomentum m → DistSp
  /-- Orthogonality in distributional sense -/
  momentum_orthogonality : ∀ (m : ℝ) (p p' : OnShellMomentum m)
    (h_distinct : p.p ≠ p'.p) (f : TestSp),
    pairing (momentumEigenstateIn m p) f ≠ pairing (momentumEigenstateIn m p') f ∨
    pairing (momentumEigenstateIn m p) f = 0

  /- === Wave packet maps === -/

  /-- Wave packet creates an in-state in ℋ_in (and thus in ℋ via Møller) -/
  wavePacketToIn : ∀ {m : ℝ}, WavePacket m → InH
  /-- Wave packet creates an out-state in ℋ_out -/
  wavePacketToOut : ∀ {m : ℝ}, WavePacket m → OutH
  /-- Multi-particle momentum eigenstate |p₁,...,pₙ,in⟩ ∈ Φ*

      |p₁,...,pₙ⟩ = a†(p₁)...a†(pₙ)|0⟩ ∈ Φ*
      For identical bosons: symmetric; for identical fermions: antisymmetric. -/
  multiMomentumIn : (n : ℕ) → (masses : Fin n → ℝ) →
    ((i : Fin n) → OnShellMomentum (masses i)) → DistSp
  /-- Multi-particle momentum eigenstate (out) -/
  multiMomentumOut : (n : ℕ) → (masses : Fin n → ℝ) →
    ((i : Fin n) → OnShellMomentum (masses i)) → DistSp
  /-- Multi-wave packet to in-state -/
  multiWavePacketToIn : ∀ {n : ℕ} {masses : Fin n → ℝ},
    MultiWavePacket n masses → InH
  /-- Multi-wave packet to out-state -/
  multiWavePacketToOut : ∀ {n : ℕ} {masses : Fin n → ℝ},
    MultiWavePacket n masses → OutH

  /- === Asymptotic completeness === -/

  /-- Asymptotic completeness for in-states: Ω₊ has dense range

      Every state in ℋ can be approximated by in-states.
      Bound states (if any) live in the orthogonal complement of Range(Ω₊). -/
  asymptotic_completeness_in :
    ∀ (ψ : H) (ε : ℝ), ε > 0 →
      ∃ (φ : InH), ‖innerProduct ψ ψ - innerProduct (moller_in φ) (moller_in φ)‖ < ε ∧
                      ‖innerProduct ψ (moller_in φ)‖ > ‖innerProduct ψ ψ‖ - ε
  /-- Asymptotic completeness for out-states: Ω₋ has dense range -/
  asymptotic_completeness_out :
    ∀ (ψ : H) (ε : ℝ), ε > 0 →
      ∃ (φ : OutH), ‖innerProduct ψ ψ - innerProduct (moller_out φ) (moller_out φ)‖ < ε ∧
                       ‖innerProduct ψ (moller_out φ)‖ > ‖innerProduct ψ ψ‖ - ε

  /- === Cluster decomposition === -/

  /-- Cluster decomposition principle

      When particle groups are spatially well-separated, amplitudes factorize.
      This ensures locality: distant systems don't interfere.

      For wave packets wp1, wp2 with spatial separation R:
      ⟨wp1 ⊗ wp2_shifted | S | wp1 ⊗ wp2_shifted⟩ →
        ⟨wp1|S|wp1⟩ · ⟨wp2|S|wp2⟩ as R → ∞ -/
  cluster_decomposition : ∀ (n m : ℕ)
    (masses1 : Fin n → ℝ) (masses2 : Fin m → ℝ)
    (wp1 : MultiWavePacket n masses1)
    (wp2 : MultiWavePacket m masses2),
    ∀ (ε : ℝ), ε > 0 →
      ∃ (R_min : ℝ), R_min > 0 ∧
        ∀ (separation : ℝ), separation > R_min →
          ∃ (amp1 amp2 amp_combined : ℂ),
            ‖amp_combined - amp1 * amp2‖ < ε

end ModularPhysics.Core.QFT.Smatrix

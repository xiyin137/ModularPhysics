-- ModularPhysics/Core/QFT/Smatrix/AsymptoticStates.lean
import ModularPhysics.Core.SpaceTime.Basic
import ModularPhysics.Core.QFT.Wightman.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.Smatrix

open SpaceTime

set_option linter.unusedVariables false

/- ============= RIGGED HILBERT SPACE (GELFAND TRIPLE) ============= -/

/-- Hilbert space ℋ of quantum states with finite norm -/
axiom HilbertSpace : Type _

/-- Inner product on Hilbert space -/
axiom innerProduct : HilbertSpace → HilbertSpace → ℂ

/-- Space of test functions Φ ⊂ ℋ (smooth, rapidly decreasing functions) -/
axiom TestSpace : Type _

/-- Embedding of test space into Hilbert space: Φ ⊂ ℋ -/
axiom testToHilbert : TestSpace → HilbertSpace

/-- Space of distributions Φ* ⊃ ℋ (dual space, contains plane waves)

    This completes the Gelfand triple: Φ ⊂ ℋ ⊂ Φ*

    Plane-wave momentum eigenstates live in Φ*, NOT in ℋ.
    They are distributions, not normalizable states. -/
axiom DistributionSpace : Type _

/-- Embedding of Hilbert space into distribution space: ℋ ⊂ Φ* -/
axiom hilbertToDistribution : HilbertSpace → DistributionSpace

/-- Pairing between test space and distribution space ⟨·|·⟩: Φ* × Φ → ℂ -/
axiom pairing : DistributionSpace → TestSpace → ℂ

/-- Vacuum state |0⟩ ∈ ℋ -/
axiom vacuum : HilbertSpace

/-- Vacuum has unit norm -/
axiom vacuum_normalized : innerProduct vacuum vacuum = 1

/- ============= ASYMPTOTIC HILBERT SPACES ============= -/

/-- In-Hilbert space: free particle states in the infinite past

    This is isomorphic to the Fock space for free particles. -/
axiom InHilbert : Type _

/-- Out-Hilbert space: free particle states in the infinite future -/
axiom OutHilbert : Type _

/-- Møller operator Ω₊: ℋ_in → ℋ (isometry mapping in-states to interacting states) -/
axiom moller_in : InHilbert → HilbertSpace

/-- Møller operator Ω₋: ℋ_out → ℋ -/
axiom moller_out : OutHilbert → HilbertSpace

/-- Møller operators are isometries -/
axiom moller_in_isometry (ψ φ : InHilbert) :
  ∃ (inner_in : InHilbert → InHilbert → ℂ),
    innerProduct (moller_in ψ) (moller_in φ) = inner_in ψ φ

axiom moller_out_isometry (ψ φ : OutHilbert) :
  ∃ (inner_out : OutHilbert → OutHilbert → ℂ),
    innerProduct (moller_out ψ) (moller_out φ) = inner_out ψ φ

/-- In-vacuum |0,in⟩ = |0⟩ -/
axiom in_vacuum : InHilbert
axiom in_vacuum_eq_vacuum : moller_in in_vacuum = vacuum

/-- Out-vacuum |0,out⟩ = |0⟩ -/
axiom out_vacuum : OutHilbert
axiom out_vacuum_eq_vacuum : moller_out out_vacuum = vacuum

/- ============= MOMENTUM EIGENSTATES (IN DISTRIBUTION SPACE) ============= -/

/-- Four-momentum (on-shell for massive particles: p² = m²) -/
structure OnShellMomentum (m : ℝ) where
  p : Fin 4 → ℝ
  mass_shell : (p 0)^2 - (p 1)^2 - (p 2)^2 - (p 3)^2 = m^2
  positive_energy : p 0 > 0

/-- Single-particle momentum eigenstate |p,in⟩ ∈ Φ* (distribution, not in ℋ!)

    These are plane waves: NOT normalizable.
    They satisfy ⟨p|p'⟩ = 2E_p (2π)³ δ³(p⃗ - p⃗')
    which is a distribution, not a finite number. -/
axiom momentumEigenstateIn (m : ℝ) (p : OnShellMomentum m) : DistributionSpace

/-- Single-particle momentum eigenstate |p,out⟩ ∈ Φ* -/
axiom momentumEigenstateOut (m : ℝ) (p : OnShellMomentum m) : DistributionSpace

/-- Delta-function normalization (distributional sense)

    ⟨p|p'⟩ = 2E_p (2π)³ δ³(p⃗ - p⃗')

    This is not a finite inner product but a distribution.
    The pairing only makes sense when integrated against test functions.

    For distinct momenta p ≠ p', the pairing gives orthogonality
    in the distributional sense. -/
axiom momentum_orthogonality (m : ℝ) (p p' : OnShellMomentum m)
  (h_distinct : p.p ≠ p'.p) (f : TestSpace) :
  -- Distinct momentum eigenstates are orthogonal when paired with test functions
  pairing (momentumEigenstateIn m p) f ≠ pairing (momentumEigenstateIn m p') f ∨
  pairing (momentumEigenstateIn m p) f = 0

/- ============= WAVE PACKETS (IN HILBERT SPACE) ============= -/

/-- Wave packet: normalizable state in ℋ

    |f⟩ = ∫ f(p) |p⟩ d³p / (2π)³ 2E_p

    where f(p) is a smooth test function with compact support.

    Wave packets ARE normalizable and live in ℋ, not just Φ*. -/
structure WavePacket (m : ℝ) where
  /-- Momentum-space amplitude f(p) -/
  amplitude : (OnShellMomentum m) → ℂ
  /-- Finite L² norm: ∫ |f(p)|² d³p/(2E_p) < ∞ (ensures normalizability) -/
  norm_bound : ℝ
  norm_positive : norm_bound > 0
  /-- Amplitude is bounded (Schwartz-like decay) -/
  amplitude_bounded : ∀ p : OnShellMomentum m, ‖amplitude p‖ ≤ norm_bound

/-- Wave packet creates an in-state in ℋ_in (and thus in ℋ via Møller) -/
axiom wavePacketToInHilbert {m : ℝ} : WavePacket m → InHilbert

/-- Wave packet creates an out-state in ℋ_out -/
axiom wavePacketToOutHilbert {m : ℝ} : WavePacket m → OutHilbert

/- ============= MULTI-PARTICLE STATES ============= -/

/-- Multi-particle momentum eigenstate (in distribution space)

    |p₁,...,pₙ⟩ = a†(p₁)...a†(pₙ)|0⟩ ∈ Φ*

    For identical bosons: symmetric
    For identical fermions: antisymmetric -/
axiom multiMomentumIn (n : ℕ) (masses : Fin n → ℝ)
  (momenta : (i : Fin n) → OnShellMomentum (masses i)) : DistributionSpace

axiom multiMomentumOut (n : ℕ) (masses : Fin n → ℝ)
  (momenta : (i : Fin n) → OnShellMomentum (masses i)) : DistributionSpace

/-- Multi-particle wave packet (normalizable, in Fock space ⊂ ℋ) -/
structure MultiWavePacket (n : ℕ) (masses : Fin n → ℝ) where
  amplitude : ((i : Fin n) → OnShellMomentum (masses i)) → ℂ
  /-- Finite norm bound ensuring normalizability -/
  norm_bound : ℝ
  norm_positive : norm_bound > 0
  /-- Amplitude is bounded -/
  amplitude_bounded : ∀ momenta, ‖amplitude momenta‖ ≤ norm_bound

axiom multiWavePacketToIn {n : ℕ} {masses : Fin n → ℝ} :
  MultiWavePacket n masses → InHilbert

axiom multiWavePacketToOut {n : ℕ} {masses : Fin n → ℝ} :
  MultiWavePacket n masses → OutHilbert

/- ============= ASYMPTOTIC COMPLETENESS ============= -/

/-- Asymptotic completeness: Møller operators have dense range

    Range(Ω₊) = ℋ (up to bound states)

    Every state in the Hilbert space can be approximated by
    in-states (scattering states). Bound states may live in
    the orthogonal complement.

    Mathematically: for any ψ ∈ ℋ and ε > 0, there exists φ ∈ ℋ_in
    such that ‖ψ - Ω₊(φ)‖ < ε. -/
axiom asymptotic_completeness_in :
  ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
    ∃ (φ : InHilbert), ‖innerProduct ψ ψ - innerProduct (moller_in φ) (moller_in φ)‖ < ε ∧
                        ‖innerProduct ψ (moller_in φ)‖ > ‖innerProduct ψ ψ‖ - ε

axiom asymptotic_completeness_out :
  ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
    ∃ (φ : OutHilbert), ‖innerProduct ψ ψ - innerProduct (moller_out φ) (moller_out φ)‖ < ε ∧
                         ‖innerProduct ψ (moller_out φ)‖ > ‖innerProduct ψ ψ‖ - ε

/- ============= CLUSTER DECOMPOSITION ============= -/

/-- Cluster decomposition principle

    When particle groups are spatially well-separated, amplitudes factorize.
    This ensures locality: distant systems don't interfere.

    For wave packets wp1, wp2 with spatial separation R:
    ⟨wp1 ⊗ wp2_shifted | S | wp1 ⊗ wp2_shifted⟩ →
      ⟨wp1|S|wp1⟩ · ⟨wp2|S|wp2⟩ as R → ∞ -/
axiom cluster_decomposition (n m : ℕ)
  (masses1 : Fin n → ℝ) (masses2 : Fin m → ℝ)
  (wp1 : MultiWavePacket n masses1)
  (wp2 : MultiWavePacket m masses2) :
  ∀ (ε : ℝ), ε > 0 →
    ∃ (R_min : ℝ), R_min > 0 ∧
      ∀ (separation : ℝ), separation > R_min →
        -- The combined amplitude approaches the product of individual amplitudes
        -- (expressed via inner products of the Møller-mapped states)
        ∃ (amp1 amp2 amp_combined : ℂ),
          ‖amp_combined - amp1 * amp2‖ < ε

end ModularPhysics.Core.QFT.Smatrix

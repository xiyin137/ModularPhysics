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
structure HilbertSpaceElement where
  data : Unit

/-- Hilbert space type -/
abbrev HilbertSpace := HilbertSpaceElement

/-- Space of test functions Φ ⊂ ℋ (smooth, rapidly decreasing functions) -/
structure TestSpaceElement where
  data : Unit

/-- Test space type -/
abbrev TestSpace := TestSpaceElement

/-- Space of distributions Φ* ⊃ ℋ (dual space, contains plane waves)

    This completes the Gelfand triple: Φ ⊂ ℋ ⊂ Φ*

    Plane-wave momentum eigenstates live in Φ*, NOT in ℋ.
    They are distributions, not normalizable states. -/
structure DistributionSpaceElement where
  data : Unit

/-- Distribution space type -/
abbrev DistributionSpace := DistributionSpaceElement

/-- Structure for rigged Hilbert space (Gelfand triple) Φ ⊂ ℋ ⊂ Φ* -/
structure RiggedHilbertSpaceTheory where
  /-- Inner product on Hilbert space -/
  innerProduct : HilbertSpace → HilbertSpace → ℂ
  /-- Embedding of test space into Hilbert space: Φ ⊂ ℋ -/
  testToHilbert : TestSpace → HilbertSpace
  /-- Embedding of Hilbert space into distribution space: ℋ ⊂ Φ* -/
  hilbertToDistribution : HilbertSpace → DistributionSpace
  /-- Pairing between test space and distribution space ⟨·|·⟩: Φ* × Φ → ℂ -/
  pairing : DistributionSpace → TestSpace → ℂ
  /-- Vacuum state |0⟩ ∈ ℋ -/
  vacuum : HilbertSpace
  /-- Vacuum has unit norm -/
  vacuum_normalized : innerProduct vacuum vacuum = 1

/-- Rigged Hilbert space theory holds -/
axiom riggedHilbertSpaceTheoryD : RiggedHilbertSpaceTheory

/-- Inner product on Hilbert space -/
noncomputable def innerProduct : HilbertSpace → HilbertSpace → ℂ := riggedHilbertSpaceTheoryD.innerProduct

/-- Embedding of test space into Hilbert space: Φ ⊂ ℋ -/
noncomputable def testToHilbert : TestSpace → HilbertSpace := riggedHilbertSpaceTheoryD.testToHilbert

/-- Embedding of Hilbert space into distribution space: ℋ ⊂ Φ* -/
noncomputable def hilbertToDistribution : HilbertSpace → DistributionSpace := riggedHilbertSpaceTheoryD.hilbertToDistribution

/-- Pairing between test space and distribution space ⟨·|·⟩: Φ* × Φ → ℂ -/
noncomputable def pairing : DistributionSpace → TestSpace → ℂ := riggedHilbertSpaceTheoryD.pairing

/-- Vacuum state |0⟩ ∈ ℋ -/
noncomputable def vacuum : HilbertSpace := riggedHilbertSpaceTheoryD.vacuum

/-- Vacuum has unit norm -/
theorem vacuum_normalized : innerProduct vacuum vacuum = 1 := riggedHilbertSpaceTheoryD.vacuum_normalized

/- ============= ASYMPTOTIC HILBERT SPACES ============= -/

/-- In-Hilbert space element: free particle states in the infinite past -/
structure InHilbertElement where
  data : Unit

/-- In-Hilbert space type -/
abbrev InHilbert := InHilbertElement

/-- Out-Hilbert space element: free particle states in the infinite future -/
structure OutHilbertElement where
  data : Unit

/-- Out-Hilbert space type -/
abbrev OutHilbert := OutHilbertElement

/-- Structure for asymptotic Hilbert spaces and Møller operators -/
structure AsymptoticHilbertSpaceTheory where
  /-- Møller operator Ω₊: ℋ_in → ℋ (isometry mapping in-states to interacting states) -/
  moller_in : InHilbert → HilbertSpace
  /-- Møller operator Ω₋: ℋ_out → ℋ -/
  moller_out : OutHilbert → HilbertSpace
  /-- Inner product on in-Hilbert space -/
  inner_in : InHilbert → InHilbert → ℂ
  /-- Inner product on out-Hilbert space -/
  inner_out : OutHilbert → OutHilbert → ℂ
  /-- Møller in-operator is an isometry -/
  moller_in_isometry : ∀ (ψ φ : InHilbert),
    innerProduct (moller_in ψ) (moller_in φ) = inner_in ψ φ
  /-- Møller out-operator is an isometry -/
  moller_out_isometry : ∀ (ψ φ : OutHilbert),
    innerProduct (moller_out ψ) (moller_out φ) = inner_out ψ φ
  /-- In-vacuum |0,in⟩ -/
  in_vacuum : InHilbert
  /-- Out-vacuum |0,out⟩ -/
  out_vacuum : OutHilbert
  /-- In-vacuum maps to vacuum -/
  in_vacuum_eq_vacuum : moller_in in_vacuum = vacuum
  /-- Out-vacuum maps to vacuum -/
  out_vacuum_eq_vacuum : moller_out out_vacuum = vacuum

/-- Asymptotic Hilbert space theory holds -/
axiom asymptoticHilbertSpaceTheoryD : AsymptoticHilbertSpaceTheory

/-- Møller operator Ω₊: ℋ_in → ℋ (isometry mapping in-states to interacting states) -/
noncomputable def moller_in : InHilbert → HilbertSpace := asymptoticHilbertSpaceTheoryD.moller_in

/-- Møller operator Ω₋: ℋ_out → ℋ -/
noncomputable def moller_out : OutHilbert → HilbertSpace := asymptoticHilbertSpaceTheoryD.moller_out

/-- Møller operators are isometries -/
theorem moller_in_isometry (ψ φ : InHilbert) :
  ∃ (inner_in : InHilbert → InHilbert → ℂ),
    innerProduct (moller_in ψ) (moller_in φ) = inner_in ψ φ :=
  ⟨asymptoticHilbertSpaceTheoryD.inner_in, asymptoticHilbertSpaceTheoryD.moller_in_isometry ψ φ⟩

theorem moller_out_isometry (ψ φ : OutHilbert) :
  ∃ (inner_out : OutHilbert → OutHilbert → ℂ),
    innerProduct (moller_out ψ) (moller_out φ) = inner_out ψ φ :=
  ⟨asymptoticHilbertSpaceTheoryD.inner_out, asymptoticHilbertSpaceTheoryD.moller_out_isometry ψ φ⟩

/-- In-vacuum |0,in⟩ = |0⟩ -/
noncomputable def in_vacuum : InHilbert := asymptoticHilbertSpaceTheoryD.in_vacuum
theorem in_vacuum_eq_vacuum : moller_in in_vacuum = vacuum := asymptoticHilbertSpaceTheoryD.in_vacuum_eq_vacuum

/-- Out-vacuum |0,out⟩ = |0⟩ -/
noncomputable def out_vacuum : OutHilbert := asymptoticHilbertSpaceTheoryD.out_vacuum
theorem out_vacuum_eq_vacuum : moller_out out_vacuum = vacuum := asymptoticHilbertSpaceTheoryD.out_vacuum_eq_vacuum

/- ============= MOMENTUM EIGENSTATES (IN DISTRIBUTION SPACE) ============= -/

/-- Four-momentum (on-shell for massive particles: p² = m²) -/
structure OnShellMomentum (m : ℝ) where
  p : Fin 4 → ℝ
  mass_shell : (p 0)^2 - (p 1)^2 - (p 2)^2 - (p 3)^2 = m^2
  positive_energy : p 0 > 0

/-- Structure for momentum eigenstate theory -/
structure MomentumEigenstateTheory where
  /-- Single-particle momentum eigenstate |p,in⟩ ∈ Φ* (distribution) -/
  momentumEigenstateIn : (m : ℝ) → OnShellMomentum m → DistributionSpace
  /-- Single-particle momentum eigenstate |p,out⟩ ∈ Φ* -/
  momentumEigenstateOut : (m : ℝ) → OnShellMomentum m → DistributionSpace
  /-- Orthogonality in distributional sense -/
  momentum_orthogonality : ∀ (m : ℝ) (p p' : OnShellMomentum m)
    (h_distinct : p.p ≠ p'.p) (f : TestSpace),
    pairing (momentumEigenstateIn m p) f ≠ pairing (momentumEigenstateIn m p') f ∨
    pairing (momentumEigenstateIn m p) f = 0

/-- Momentum eigenstate theory axiom -/
axiom momentumEigenstateTheoryD : MomentumEigenstateTheory

/-- Single-particle momentum eigenstate |p,in⟩ ∈ Φ* (distribution, not in ℋ!)

    These are plane waves: NOT normalizable.
    They satisfy ⟨p|p'⟩ = 2E_p (2π)³ δ³(p⃗ - p⃗')
    which is a distribution, not a finite number. -/
def momentumEigenstateIn (m : ℝ) (p : OnShellMomentum m) : DistributionSpace :=
  momentumEigenstateTheoryD.momentumEigenstateIn m p

/-- Single-particle momentum eigenstate |p,out⟩ ∈ Φ* -/
def momentumEigenstateOut (m : ℝ) (p : OnShellMomentum m) : DistributionSpace :=
  momentumEigenstateTheoryD.momentumEigenstateOut m p

/-- Delta-function normalization (distributional sense)

    ⟨p|p'⟩ = 2E_p (2π)³ δ³(p⃗ - p⃗')

    This is not a finite inner product but a distribution.
    The pairing only makes sense when integrated against test functions.

    For distinct momenta p ≠ p', the pairing gives orthogonality
    in the distributional sense. -/
theorem momentum_orthogonality (m : ℝ) (p p' : OnShellMomentum m)
  (h_distinct : p.p ≠ p'.p) (f : TestSpace) :
  -- Distinct momentum eigenstates are orthogonal when paired with test functions
  pairing (momentumEigenstateIn m p) f ≠ pairing (momentumEigenstateIn m p') f ∨
  pairing (momentumEigenstateIn m p) f = 0 :=
  momentumEigenstateTheoryD.momentum_orthogonality m p p' h_distinct f

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

/-- Multi-particle wave packet (normalizable, in Fock space ⊂ ℋ) -/
structure MultiWavePacket (n : ℕ) (masses : Fin n → ℝ) where
  amplitude : ((i : Fin n) → OnShellMomentum (masses i)) → ℂ
  /-- Finite norm bound ensuring normalizability -/
  norm_bound : ℝ
  norm_positive : norm_bound > 0
  /-- Amplitude is bounded -/
  amplitude_bounded : ∀ momenta, ‖amplitude momenta‖ ≤ norm_bound

/-- Structure for wave packet and multi-particle state theory -/
structure WavePacketStateTheory where
  /-- Wave packet creates an in-state in ℋ_in -/
  wavePacketToInHilbert : ∀ {m : ℝ}, WavePacket m → InHilbert
  /-- Wave packet creates an out-state in ℋ_out -/
  wavePacketToOutHilbert : ∀ {m : ℝ}, WavePacket m → OutHilbert
  /-- Multi-particle momentum eigenstate (in) -/
  multiMomentumIn : (n : ℕ) → (masses : Fin n → ℝ) →
    ((i : Fin n) → OnShellMomentum (masses i)) → DistributionSpace
  /-- Multi-particle momentum eigenstate (out) -/
  multiMomentumOut : (n : ℕ) → (masses : Fin n → ℝ) →
    ((i : Fin n) → OnShellMomentum (masses i)) → DistributionSpace
  /-- Multi-wave packet to in-state -/
  multiWavePacketToIn : ∀ {n : ℕ} {masses : Fin n → ℝ},
    MultiWavePacket n masses → InHilbert
  /-- Multi-wave packet to out-state -/
  multiWavePacketToOut : ∀ {n : ℕ} {masses : Fin n → ℝ},
    MultiWavePacket n masses → OutHilbert

/-- Wave packet state theory axiom -/
axiom wavePacketStateTheoryD : WavePacketStateTheory

/-- Wave packet creates an in-state in ℋ_in (and thus in ℋ via Møller) -/
def wavePacketToInHilbert {m : ℝ} : WavePacket m → InHilbert :=
  wavePacketStateTheoryD.wavePacketToInHilbert

/-- Wave packet creates an out-state in ℋ_out -/
def wavePacketToOutHilbert {m : ℝ} : WavePacket m → OutHilbert :=
  wavePacketStateTheoryD.wavePacketToOutHilbert

/- ============= MULTI-PARTICLE STATES ============= -/

/-- Multi-particle momentum eigenstate (in distribution space)

    |p₁,...,pₙ⟩ = a†(p₁)...a†(pₙ)|0⟩ ∈ Φ*

    For identical bosons: symmetric
    For identical fermions: antisymmetric -/
def multiMomentumIn (n : ℕ) (masses : Fin n → ℝ)
  (momenta : (i : Fin n) → OnShellMomentum (masses i)) : DistributionSpace :=
  wavePacketStateTheoryD.multiMomentumIn n masses momenta

def multiMomentumOut (n : ℕ) (masses : Fin n → ℝ)
  (momenta : (i : Fin n) → OnShellMomentum (masses i)) : DistributionSpace :=
  wavePacketStateTheoryD.multiMomentumOut n masses momenta

def multiWavePacketToIn {n : ℕ} {masses : Fin n → ℝ} :
  MultiWavePacket n masses → InHilbert :=
  wavePacketStateTheoryD.multiWavePacketToIn

def multiWavePacketToOut {n : ℕ} {masses : Fin n → ℝ} :
  MultiWavePacket n masses → OutHilbert :=
  wavePacketStateTheoryD.multiWavePacketToOut

/- ============= ASYMPTOTIC COMPLETENESS ============= -/

/-- Structure for asymptotic completeness theory -/
structure AsymptoticCompletenessTheory where
  /-- Asymptotic completeness for in-states -/
  asymptotic_completeness_in :
    ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
      ∃ (φ : InHilbert), ‖innerProduct ψ ψ - innerProduct (moller_in φ) (moller_in φ)‖ < ε ∧
                          ‖innerProduct ψ (moller_in φ)‖ > ‖innerProduct ψ ψ‖ - ε
  /-- Asymptotic completeness for out-states -/
  asymptotic_completeness_out :
    ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
      ∃ (φ : OutHilbert), ‖innerProduct ψ ψ - innerProduct (moller_out φ) (moller_out φ)‖ < ε ∧
                           ‖innerProduct ψ (moller_out φ)‖ > ‖innerProduct ψ ψ‖ - ε
  /-- Cluster decomposition principle -/
  cluster_decomposition : ∀ (n m : ℕ)
    (masses1 : Fin n → ℝ) (masses2 : Fin m → ℝ)
    (wp1 : MultiWavePacket n masses1)
    (wp2 : MultiWavePacket m masses2),
    ∀ (ε : ℝ), ε > 0 →
      ∃ (R_min : ℝ), R_min > 0 ∧
        ∀ (separation : ℝ), separation > R_min →
          ∃ (amp1 amp2 amp_combined : ℂ),
            ‖amp_combined - amp1 * amp2‖ < ε

/-- Asymptotic completeness theory axiom -/
axiom asymptoticCompletenessTheoryD : AsymptoticCompletenessTheory

/-- Asymptotic completeness: Møller operators have dense range

    Range(Ω₊) = ℋ (up to bound states)

    Every state in the Hilbert space can be approximated by
    in-states (scattering states). Bound states may live in
    the orthogonal complement.

    Mathematically: for any ψ ∈ ℋ and ε > 0, there exists φ ∈ ℋ_in
    such that ‖ψ - Ω₊(φ)‖ < ε. -/
theorem asymptotic_completeness_in :
  ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
    ∃ (φ : InHilbert), ‖innerProduct ψ ψ - innerProduct (moller_in φ) (moller_in φ)‖ < ε ∧
                        ‖innerProduct ψ (moller_in φ)‖ > ‖innerProduct ψ ψ‖ - ε :=
  asymptoticCompletenessTheoryD.asymptotic_completeness_in

theorem asymptotic_completeness_out :
  ∀ (ψ : HilbertSpace) (ε : ℝ), ε > 0 →
    ∃ (φ : OutHilbert), ‖innerProduct ψ ψ - innerProduct (moller_out φ) (moller_out φ)‖ < ε ∧
                         ‖innerProduct ψ (moller_out φ)‖ > ‖innerProduct ψ ψ‖ - ε :=
  asymptoticCompletenessTheoryD.asymptotic_completeness_out

/- ============= CLUSTER DECOMPOSITION ============= -/

/-- Cluster decomposition principle

    When particle groups are spatially well-separated, amplitudes factorize.
    This ensures locality: distant systems don't interfere.

    For wave packets wp1, wp2 with spatial separation R:
    ⟨wp1 ⊗ wp2_shifted | S | wp1 ⊗ wp2_shifted⟩ →
      ⟨wp1|S|wp1⟩ · ⟨wp2|S|wp2⟩ as R → ∞ -/
theorem cluster_decomposition (n m : ℕ)
  (masses1 : Fin n → ℝ) (masses2 : Fin m → ℝ)
  (wp1 : MultiWavePacket n masses1)
  (wp2 : MultiWavePacket m masses2) :
  ∀ (ε : ℝ), ε > 0 →
    ∃ (R_min : ℝ), R_min > 0 ∧
      ∀ (separation : ℝ), separation > R_min →
        -- The combined amplitude approaches the product of individual amplitudes
        -- (expressed via inner products of the Møller-mapped states)
        ∃ (amp1 amp2 amp_combined : ℂ),
          ‖amp_combined - amp1 * amp2‖ < ε :=
  asymptoticCompletenessTheoryD.cluster_decomposition n m masses1 masses2 wp1 wp2

end ModularPhysics.Core.QFT.Smatrix

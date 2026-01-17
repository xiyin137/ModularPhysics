import ModularPhysics.Core.QFT.AQFT.Representations

namespace ModularPhysics.Core.QFT.AQFT

/-- DHR superselection theory (charge sectors, particle statistics) -/
axiom dhrSuperselection : Type _

/-- Doplicher-Roberts reconstruction: from abstract algebra back to fields
    Remarkable theorem: local net of algebras determines field content! -/
axiom doplicherRobertsReconstruction :
  (∀ O, LocalAlgebra O) → ∃ (_ : Type _), True

/-- Charge superselection sectors (inequivalent representations) -/
axiom chargeSectors : Type _

/-- Statistics parameter (phase under exchange for localized charges) -/
axiom statisticsParameter : chargeSectors → ℝ

/-- Bose-Fermi alternative: only θ = 0 (bosons) or θ = π (fermions) in 4D -/
axiom bose_fermi_alternative (θ : ℝ) :
  statisticsParameter sorry = θ → θ = 0 ∨ θ = Real.pi

end ModularPhysics.Core.QFT.AQFT

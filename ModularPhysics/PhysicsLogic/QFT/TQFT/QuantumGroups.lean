import ModularPhysics.PhysicsLogic.QFT.TQFT.ModularTensorCategories
import ModularPhysics.PhysicsLogic.QFT.TQFT.ChernSimons
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.TQFT

set_option linter.unusedVariables false

/- ============= QUANTUM GROUPS ============= -/

/-- Quantum group data Uq(g).

    A quantum group is a Hopf algebra deformation of a universal
    enveloping algebra U(g), depending on a parameter q ∈ ℂ*.

    When q is a root of unity, the representation category of Uq(g)
    is a modular tensor category — this is the algebraic foundation
    for the Reshetikhin-Turaev construction of 3D TQFTs.

    Parameterized by a Lie algebra (from ChernSimons) and deformation parameter q. -/
structure QuantumGroupData where
  /-- Abstract Lie algebra type (labels the quantum group) -/
  LieAlgebra : Type
  /-- Deformation parameter q ∈ ℂ* -/
  q : ℂ
  /-- q is nonzero -/
  q_ne_zero : q ≠ 0
  /-- Abstract quantum group element type Uq(g) -/
  Element : Type
  /-- Multiplication in the quantum group -/
  mul : Element → Element → Element
  /-- Unit -/
  one : Element
  /-- Comultiplication (Hopf algebra structure) Δ : Uq(g) → Uq(g) ⊗ Uq(g) -/
  ComulTarget : Type
  comul : Element → ComulTarget

/-- Representation of a quantum group. -/
structure QuantumRepData (qg : QuantumGroupData) where
  /-- Carrier type of the representation -/
  Carrier : Type
  /-- Dimension of the representation -/
  dim : ℕ
  /-- Dimension is positive -/
  dim_pos : dim > 0
  /-- Action of quantum group on carrier -/
  action : qg.Element → Carrier → Carrier

/-- Quantum group theory: connects quantum groups to MTCs and TQFTs.

    The key insight is that Rep(Uq(g)) at q = root of unity
    forms a modular tensor category, which via the RT construction
    gives a 3D TQFT equivalent to Chern-Simons theory. -/
structure QuantumGroupTheoryData {md : StandaloneManifoldData} {cs : ChernSimonsData md}
    (mtc : MTCData md cs) where
  /-- Quantum dimension of a representation (modified dimension in semisimple category)

      dim_q(V) = tr_q(id_V) where tr_q is the quantum trace.
      At generic q: dim_q(V_n) = [n+1]_q = (q^{n+1} - q^{-n-1})/(q - q^{-1}).
      At root of unity: truncation to finitely many simples. -/
  quantumRepDimension : (qg : QuantumGroupData) → QuantumRepData qg → ℂ
  /-- Quantum trace (categorical trace in the ribbon category) -/
  quantumTrace : (qg : QuantumGroupData) → QuantumRepData qg → ℂ
  /-- Rep(Uq(g)) at root of unity forms modular tensor category

      When q = e^{2πi/(k+h∨)} (h∨ = dual Coxeter number),
      the semisimplified representation category is an MTC
      with rank determined by k and g. -/
  quantumGroupMTC : QuantumGroupData → ModularTensorCategory

end ModularPhysics.Core.QFT.TQFT

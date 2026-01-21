import ModularPhysics.Core.QFT.TQFT.ModularTensorCategories
import ModularPhysics.Core.QFT.TQFT.ChernSimons
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.TQFT

set_option linter.unusedVariables false

/-- Quantum group element Uq(g) -/
structure QuantumGroupElement (g : LieAlgebra) (q : ℂ) where
  data : Unit

/-- Quantum group type -/
abbrev QuantumGroup (g : LieAlgebra) (q : ℂ) := QuantumGroupElement g q

/-- Representation of quantum group element -/
structure QuantumRepElement {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q) where
  data : Unit

/-- Representation of quantum group type -/
abbrev QuantumRep {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q) := QuantumRepElement Uq

/-- Quantum group theory structure -/
structure QuantumGroupTheory where
  /-- Quantum dimension of a representation (modified dimension in semisimple category) -/
  quantumRepDimension : {g : LieAlgebra} → {q : ℂ} → (Uq : QuantumGroup g q) →
    QuantumRep Uq → ℂ
  /-- Quantum trace -/
  quantumTrace : {g : LieAlgebra} → {q : ℂ} → (Uq : QuantumGroup g q) →
    QuantumRep Uq → ℂ
  /-- Rep(Uq(g)) at root of unity forms modular tensor category -/
  quantumGroupMTC : {g : LieAlgebra} → {q : ℂ} → QuantumGroup g q → ModularTensorCategory

/-- Quantum group theory holds -/
axiom quantumGroupTheoryD : QuantumGroupTheory

/-- Quantum dimension of a representation (modified dimension in semisimple category) -/
noncomputable def quantumRepDimension {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q)
  (V : QuantumRep Uq) : ℂ :=
  quantumGroupTheoryD.quantumRepDimension Uq V

/-- Quantum trace -/
noncomputable def quantumTrace {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q)
  (V : QuantumRep Uq) : ℂ :=
  quantumGroupTheoryD.quantumTrace Uq V

/-- Rep(Uq(g)) at root of unity forms modular tensor category -/
noncomputable def quantumGroupMTC {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q) :
  ModularTensorCategory :=
  quantumGroupTheoryD.quantumGroupMTC Uq

end ModularPhysics.Core.QFT.TQFT
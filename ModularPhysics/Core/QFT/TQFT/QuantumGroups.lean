import ModularPhysics.Core.QFT.TQFT.ModularTensorCategories
import ModularPhysics.Core.QFT.TQFT.ChernSimons
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Core.QFT.TQFT

set_option linter.unusedVariables false

/-- Quantum group Uq(g) -/
axiom QuantumGroup (g : LieAlgebra) (q : ℂ) : Type

/-- Representation of quantum group -/
axiom QuantumRep {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q) : Type

/-- Quantum dimension (modified dimension in semisimple category) -/
noncomputable axiom quantumDimension {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q)
  (V : QuantumRep Uq) : ℂ

/-- Quantum trace -/
noncomputable axiom quantumTrace {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q)
  (V : QuantumRep Uq) : ℂ

/-- Rep(Uq(g)) at root of unity forms modular tensor category -/
axiom quantumGroupMTC {g : LieAlgebra} {q : ℂ} (Uq : QuantumGroup g q) : ModularTensorCategory

end ModularPhysics.Core.QFT.TQFT
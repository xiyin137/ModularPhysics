-- ModularPhysics/Core/QFT/RG.lean
-- Re-exports all RG modules

import ModularPhysics.PhysicsLogic.QFT.RG.Basic
import ModularPhysics.PhysicsLogic.QFT.RG.WilsonianRG
import ModularPhysics.PhysicsLogic.QFT.RG.GellMannLow
import ModularPhysics.PhysicsLogic.QFT.RG.EffectiveAction

namespace ModularPhysics.Core.QFT.RG

/-!
# Renormalization Group

This module collects the renormalization group formalism:

- `Basic`: Fundamental concepts (scales, operators, beta functions, fixed points)
- `WilsonianRG`: Wilsonian effective action, exact RG, Polchinski equation
- `GellMannLow`: Perturbative RG, Callan-Symanzik, running couplings
- `EffectiveAction`: 1PI effective action, effective potential, Coleman-Weinberg
-/

end ModularPhysics.Core.QFT.RG

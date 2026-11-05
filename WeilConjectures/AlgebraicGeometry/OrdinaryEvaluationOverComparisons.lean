/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
import WeilConjectures.AlgebraicGeometry.HomComplexOverEquivProjections
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula

/-! # Compatible ordinary evaluation comparisons on the open scheme

Source: Stacks Project, Tags 08DL, 08DJ and 08DQ, ordinary complex constructions.
(blueprint: lem-pc-ordinary-evaluation-over-comparisons).
No acyclicity, quasi-isomorphism or K-injectivity assertion is included here. -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- The public existential dual witness is intentionally independent of the tensor witness.

end AlgebraicGeometry

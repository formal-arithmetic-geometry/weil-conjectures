/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationSourceBiproduct
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationTargetBiproduct
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock
import WeilConjectures.Algebra.Homology.HomComplex

/-! # Finite-support assembly of ordinary evaluation

Source: Stacks Project, Tags 08DQ and 08DM, finite total-complex calculation.
(blueprint: lem-pc-bounded-ordinary-evaluation-assembly).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] localEvaluationPreadditive

end AlgebraicGeometry

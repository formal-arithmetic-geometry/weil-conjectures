/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationTensorSummands
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentOverTransport

/-! # Tensor summand calculation for ordinary evaluation under open reindexing

Source: Stacks Project, Tags 0A8X, 08DL and 08DQ, ordinary Hom and evaluation.
(blueprint: lem-pc-ordinary-evaluation-over-tensor-formula). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local irreducible] homComplexFunctor IsSchemeOrdinaryEvaluation

end AlgebraicGeometry

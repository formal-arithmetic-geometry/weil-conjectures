/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverComparisons
import WeilConjectures.AlgebraicGeometry.TotalTensorOverEquivIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Transport of ordinary evaluation across the open-site equivalence
Source: Stacks Project, Tags 08DL, 08DJ and 08DQ; Mathlib `Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-over-transport).
This is a statement about actual complexes only. It mentions neither RHom nor
canonical derived evaluation nor an arbitrary derived representative.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

section TransportProofs

end TransportProofs

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.LocalizedOpenTensorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Total tensor comparison for the open-site equivalence

Source: Stacks Project, Tags 06YN and 08DJ, ordinary tensor totalization;
Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-total-tensor-over-equiv-iso). -/

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

end AlgebraicGeometry

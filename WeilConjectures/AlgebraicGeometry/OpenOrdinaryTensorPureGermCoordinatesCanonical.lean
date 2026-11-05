/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedTensorRestrictionStalkUnit
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import all WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison

/-! # Unit-scalar generators and scalar extension for the pinned tensor comparison

Source: Stacks Project, Tags 0098 and 0096.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
open TopologicalSpace Opposite

end AlgebraicGeometry

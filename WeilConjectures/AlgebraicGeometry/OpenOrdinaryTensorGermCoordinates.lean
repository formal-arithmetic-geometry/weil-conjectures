/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorStalkRingCoordinates
import WeilConjectures.AlgebraicGeometry.SemilinearTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorPureGermCoordinates
import WeilConjectures.AlgebraicGeometry.OpenSemilinearInputComplexIso

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange

end AlgebraicGeometry

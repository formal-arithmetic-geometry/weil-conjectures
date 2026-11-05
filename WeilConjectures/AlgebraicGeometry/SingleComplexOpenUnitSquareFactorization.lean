/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedCounitUnit

/-! # Normalizing the derived unit through the open pullback square

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Keep derived universal-property constructions abstract during the square calculation.
-- Only the final conversion needs to compare the underlying category instances.
attribute [local irreducible] singleComplexOpenPullbackIso CategoryTheory.Functor.mapDerivedCategory

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Cancelling the restricted homotopy counit comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Keep constructed functors abstract; expose only category aliases to implicit unification.
attribute [local irreducible] singleComplexOpenPullbackIso Functor.mapHomotopyCategory
  Functor.mapDerivedCategory openPinnedHomotopyTensorRestrictionIso
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom TopCat.Sheaf
  DerivedCategory HomotopyCategory

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Category.Grp.AB

/-!
# Connecting-map factorization for the Milnor sequence

Source: Stacks Project, More on Algebra, Tags 07KW and 07KY.
(blueprint: lem-pc-milnor-boundary-factorization).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
noncomputable section
attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

end
end CategoryTheory

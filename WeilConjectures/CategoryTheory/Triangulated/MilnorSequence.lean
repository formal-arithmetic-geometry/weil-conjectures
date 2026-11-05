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
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.Triangulated.MilnorBoundaryFactorization
import WeilConjectures.CategoryTheory.Triangulated.MilnorProjectionFactorization

/-!
# Milnor exact sequence for a derived inverse limit

Source: Stacks Project, More on Algebra, Tags 07KY and 08U5;
Derived Categories of Schemes, Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-milnor-sequence).

The maps are chosen simultaneously for all specified Roos triangles and are natural
for morphisms of these triangles. No functorial choice of a derived-limit object is assumed.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

noncomputable section

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

end
end CategoryTheory

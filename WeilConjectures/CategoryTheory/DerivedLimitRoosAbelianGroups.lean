/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RoosAcyclicResolution
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.InjectiveTowerEmbedding
import WeilConjectures.CategoryTheory.InjectiveSplitTower

/-!
# Roos computation of derived limits of abelian groups

Source: Stacks Project, More on Algebra, Lemma 15.88.1, Tag 07KW
(blueprint: lem-pc-derived-limit-roos-abelian-groups).

## Main statements

- `roosTowerEnoughInjectives`: the tower category has enough injectives.
- `roosLimitAdditive`: inverse limit is additive.
- `derivedLimitRoosAbelianGroups`: inverse limit is left exact, naturally the kernel of
  the Roos map; its first right derived functor is naturally the cokernel and higher
  right derived functors vanish.

We use the Mathlib functor category for towers, reindexing positive integers by `n + 1`.
All groups lie in an arbitrary universe `u`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] roosTowerEnoughInjectives

attribute [local instance] roosLimitAdditive

end CategoryTheory

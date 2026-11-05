/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SmallCechFreeExact
public import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Free Yoneda comparison with the categorical Čech cochains

Source: Stacks Project, Cohomology on Sites, Tag 03AS.
-/

@[expose] public section

universe u v

namespace CategoryTheory.SmallCech

open CategoryTheory Limits Opposite

variable {C : Type u} [Category.{v} C] (X : C)

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable [HasFiniteWidePullbacks C] {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})

end CategoryTheory.SmallCech

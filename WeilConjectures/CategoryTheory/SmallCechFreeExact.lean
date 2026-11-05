/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Small free abelian presheaf chains of a Čech family

Source: Stacks Project, Cohomology on Sites, Tags 03AS, 03AT and 03AU.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

namespace SmallCech

variable {C : Type u} [Category.{v} C] (X : C)

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable [HasFiniteWidePullbacks C] {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X)

-- The following constructions are made at one fixed presheaf argument. A lift
-- is selected by its composite to X, so all faces select the same lift.

-- Extend the prefix and deletion functions by the free abelian group functor.

-- The first face is the identity; successor faces cancel the other composite.

end SmallCech
end CategoryTheory

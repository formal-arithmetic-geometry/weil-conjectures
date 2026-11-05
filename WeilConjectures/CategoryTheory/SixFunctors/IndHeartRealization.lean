/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Presentable.Finite
/-!
# Realizing ind-objects of a finitely presentable full subcategory

Source: blueprint main-20261015, sk-prop-ind-heart,
`sk-prop-ind-heart-full-faithfulness.proof.md`, paragraphs (2) and the statement's image clause.
(blueprint: det-ind-heart-full-faithfulness-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v u u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor

namespace IndRealization
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (F : C ⥤ D) [HasFilteredColimits D]

end IndRealization

open IndRealization
namespace CategoryTheory

end CategoryTheory

namespace CategoryTheory
end CategoryTheory

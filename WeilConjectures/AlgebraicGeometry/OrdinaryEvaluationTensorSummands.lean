/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.LocalizedOpenSheafification
import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-! # Normalized tensor summands under the open-site equivalence

Source: Stacks Project, Tag 0A8X, ordinary tensor totalization; the open-site
reindexing construction in Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-tensor-summands). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

open BraidedCategory Functor MonoidalCategory.Functor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
-- The proof uses the equivalence API, never its large sectionwise implementation.
attribute [local irreducible] Scheme.Modules.overEquiv

section Normalize
universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable [BraidedCategory C] [BraidedCategory D]

end Normalize

section Descent
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

end Descent

end AlgebraicGeometry

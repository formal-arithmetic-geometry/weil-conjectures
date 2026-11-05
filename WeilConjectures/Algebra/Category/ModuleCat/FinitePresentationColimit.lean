/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Finitely presented modules and filtered colimits

Let `F : J ⥤ ModuleCat R` be a filtered diagram whose colimit is computed on underlying types,
with colimit cocone `c`. A linear map from a finitely presented module `M` to the colimit
`c.pt` factors through some `F.obj j`
(`ModuleCat.exists_lift_of_isColimit_of_finitePresentation`): the images of finitely many
generators lift to a common stage, and the finitely many relations, which hold in the colimit,
already hold at a later stage.
-/

@[expose] public section

universe w r v u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R] {J : Type w} [Category.{r} J] [IsFiltered J]
  {F : J ⥤ ModuleCat.{v} R} [PreservesColimit F (forget (ModuleCat.{v} R))]
  {c : Cocone F} (hc : IsColimit c)

end ModuleCat

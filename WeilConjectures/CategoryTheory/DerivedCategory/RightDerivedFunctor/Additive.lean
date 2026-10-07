/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-!
# Additivity of the right derived functor

The right derived functor `F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` of an
additive functor `F` between abelian categories, where `C` has K-injective resolutions, is
additive: it is computed on K-injective representatives, on which it is induced by the additive
functor `F` on homotopy categories, and the localization functors are additive.
-/

@[expose] public section

open CategoryTheory Abelian

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]

/-- **The right derived functor of an additive functor is additive.** -/
instance CategoryTheory.Functor.additive_rightDerivedFunctor (F : C ⥤ D) [F.Additive] :
    F.rightDerivedFunctor.Additive :=
  sorry

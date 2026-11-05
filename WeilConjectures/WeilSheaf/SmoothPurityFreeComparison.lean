/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree

/-!
# Comparing free Weil objects with compact-support functors

The coproduct proof for a right derived pushforward only needs its comparisons with
forgetting and the cyclic actions. We state that proof for arbitrary functors, so it
also applies to composites with exact extension by zero.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  (RW : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
  (R : DerivedCategory C ⥤ DerivedCategory D)
  (e : RW ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ R)

variable (χ : R ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ R)
  (hσ : ∀ A : DerivedCategory (IsoAlgebra F),
    (derivedStrIso G).hom.app (RW.obj A) ≫ e.hom.app A =
      G.mapDerivedCategory.map (e.hom.app A) ≫
        χ.hom.app ((forget F).mapDerivedCategory.obj A) ≫
        R.map ((derivedStrIso F).hom.app A))

include hσ

end CategoryTheory.Endofunctor.IsoAlgebra

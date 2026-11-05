/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility

/-! # Natural comparison for abelian higher direct images

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-higher-direct-image-natural-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The derived-Hom presentation of restricted cohomology, for degree-zero coefficients.
This is the presheaf in Tag 03Q8, before sheafification. -/
noncomputable abbrev abelianHigherDirectImageRawPresheaf {S Y : Scheme.{v}}
    (h : Y ⟶ S) (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
  (uliftYoneda.{v + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} ⋙
    upperStar AddCommGrpCat.{v + 1} h ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)

/-- Pull back a raw derived-Hom class and then apply the coefficient map.
All factors are actual functorial constructions: pullback composition, comparison
with the degree-zero single functor, pullback of the class, shift comparison, and
shifted coefficient map. Source: Stacks Project, Tag 09Z1, cohomology comparison. -/
noncomputable def abelianHigherDirectImageRawPullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (U : S.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    (abelianHigherDirectImageRawPresheaf h' p F').obj (op U) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app _) ≫
    (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((a)^*[AddCommGrpCat.{v + 1}]).map z ≫
    (D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (p : ℤ)).map
      ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

end AlgebraicGeometry.Etale

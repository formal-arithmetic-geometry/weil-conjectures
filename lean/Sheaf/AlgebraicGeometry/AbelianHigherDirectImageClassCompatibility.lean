/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Pullback compatibility of the canonical derived-Hom class map

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-higher-direct-image-class-compatibility).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The free abelian sheaf on an etale representable, constructed by sheafification. -/
noncomputable abbrev abelianComparisonFree (S : Scheme.{v}) :=
  uliftYoneda.{v + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}

/-- Shift compatibility identifies zeroth homology of the shifted direct image with
its degree-p homology. Both factors are the specified canonical comparisons. -/
noncomputable def abelianComparisonShift {S Y : Scheme.{v}} (h : Y ⟶ S) (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)) ≅
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((R+((h)_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso (p : ℤ) 0 (p : ℤ)
      (add_zero (p : ℤ))).app _

/-- Send a raw class to a section by derived adjunction, zeroth homology, shift
comparison, and evaluation at the identity generator. This constructs the map;
it makes no choice from the mere existence of an isomorphism. -/
noncomputable def abelianHigherDirectImageClass {S Y : Scheme.{v}} (h : Y ⟶ S)
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{v + 1}]).obj ((abelianComparisonFree S).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) :
    ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op U) :=
  (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus.homEquiv _ _
          ((((h)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            ((abelianComparisonFree S).obj U) ≫ z)) ≫
      (abelianComparisonShift h p F).hom).hom.app (op U)).hom
    (((toSheafify S.smallEtaleTopology
      (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U)).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 U))))

/-- The explicit class map commutes with pullback of a raw class and the canonical
higher-direct-image transition. Source: Stacks Project, Tag 03Q8 (the canonical
sectionwise comparison), Tag 09Z1 (compatibility of comparison maps).
(blueprint: lem-sbc-abelian-higher-direct-image-class-compatibility).

Proof: Write the adjunct of z as the derived unit followed by the direct image
of the single-functor comparison and z. Expand the higher-image transition as
its defining derived unit, pullback-composition comparison, counit, and coefficient
map. Naturality of the derived unit moves z through the pullback. The triangle
identity cancels the counit with the unit. The coherence of the exact pullback
single-functor comparison and the pullback-composition comparison identifies
the remaining source factor with the single of upperStarComp. Naturality of the
shift comparison moves the shifted coefficient map to the right and identifies
the result with the adjunct of the displayed pulled-back class. Applying zeroth
homology, its single-functor comparison, and the shift-to-degree-p comparison
preserves this equality. Finally evaluate at the identity generator. These are
identities of actual adjunctions and functors, valid for all schemes and all
nonnegative degrees; no geometric finiteness assumptions enter. -/
theorem abelianHigherDirectImageClass_pullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{v + 1}]).obj ((abelianComparisonFree S).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) :
    (abelianHigherDirectImageMap a h h' w p F F' φ).hom.app (op U)
        (abelianHigherDirectImageClass h p F U z) =
      abelianHigherDirectImageClass h' p F' U
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app _) ≫
          (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
          D+((a)^*[AddCommGrpCat.{v + 1}]).map z ≫
          (D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (shiftFunctor _ (p : ℤ)).map
            ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
              (DerivedCategory.Plus.singleFunctor _ 0).map φ)) := by sorry

end AlgebraicGeometry.Etale

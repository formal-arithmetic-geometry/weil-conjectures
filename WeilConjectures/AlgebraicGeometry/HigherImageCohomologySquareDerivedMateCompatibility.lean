/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareRawMap
public import WeilConjectures.AlgebraicGeometry.RelativeHigherDirectImageExchange
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.RelativeHigherDirectImageExchange
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareRepresentedGeneratorTransport
import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareCoefficientShiftNaturality
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- Derived-mate compatibility before restricted cohomology evaluation.
Source: Stacks Project, Tags 03Q8, 07A7 and 0EYM.
(blueprint: lem-sf-higher-image-cohomology-square-derived-mate-compatibility). -/
theorem higherImageCohomologySquare_derived_mate_compatibility
    {Y Y' S S' : Scheme.{u}}
    {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F')
    (p : ℕ) {W : S.Etale} {W' : S'.Etale}
    (v : W'.left ⟶ W.left) (hv : v ≫ W.hom = W'.hom ≫ b)
    (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op W)) :
    (let H := (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
     let U := (MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) b).obj W
     let l : W' ⟶ U := MorphismProperty.Over.homMk
       (Limits.pullback.lift v W'.hom (by simpa [U] using hv)) (by simp [U])
     (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).unit.app H).hom.app
          (op W) ≫
       ((upperStar AddCommGrpCat.{u + 1} b).obj H).obj.map l.op ≫
       (relativeHigherDirectImageExchange sq F F' φ p).hom.app (op W'))
       ((higherDirectImagePresheafToHomologyAbelian h (p : ℤ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).app (op W) z)) =
      (higherDirectImagePresheafToHomologyAbelian h' (p : ℤ)
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F')).app (op W')
        ((DerivedCategory.Plus.singleFunctor _ 0).map
          (higherImageCohomologySquareRawSource sq v hv) ≫
          ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor
            0).inv.app
              ((upperStar AddCommGrpCat.{u + 1} h).obj
                ((abelianComparisonFree S).obj W)) ≫
          (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map z ≫
          ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.commShiftIso
            (p : ℤ)).hom.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (shiftFunctor _ (p : ℤ)).map
            (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor
              0).hom.app F ≫ (DerivedCategory.Plus.singleFunctor _ 0).map φ)) := by
  sorry
end AlgebraicGeometry.Etale

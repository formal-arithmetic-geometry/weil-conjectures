/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import WeilConjectures.SixFunctors.BaseChange.UniversalHomeomorphism
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf

/-! # Transport of constant higher direct images across isomorphic squares

Source: Stacks Project, Tag 0F1I, identification of the Cartesian generic-fibre diagram.
(blueprint: lem-kun-constant-higher-direct-image-square-iso)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private noncomputable def constantAbelianPullbackIso {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        upperStar AddCommGrpCat.{u + 1} g ≅
      constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).comp
    (upperStarLowerStarAdjunction _ g)).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))).leftAdjointUniq
    (constantSheafAdj _ _ (isTerminalOverPullbackObjMkId g))

/-- Vanishing of a constant higher direct image is unchanged by an isomorphic
Cartesian presentation. Pullback by the base isomorphism is an equivalence. Its
homology comparison and derived base change identify the pulled-back higher direct
image with the higher direct image on the new square. The single-complex comparison
and the constant-sheaf pullback comparison identify the coefficient with the same
constant sheaf. Reflect the zero object through the equivalence.
Source: Stacks Project, Tag 0F1I, Cartesian generic-fibre identification.
(blueprint: lem-kun-constant-higher-direct-image-square-iso) -/
theorem isZero_constantHigherDirectImage_of_isomorphic_square
    {Y Y' X X' : Scheme.{u}} {a : Y' ⟶ Y} {h' : Y' ⟶ X'}
    {h : Y ⟶ X} {b : X' ⟶ X} (sq : IsPullback a h' h b) [IsIso b]
    (M : AddCommGrpCat.{u + 1}) (q : ℤ)
    (hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((lowerStar AddCommGrpCat.{u + 1} h').rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M))))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)))) := by
  let A := AddCommGrpCat.{u + 1}
  let F := (constantSheaf Y.smallEtaleTopology A).obj M
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let U := upperStar A b
  let V := upperStar A a
  have : IsIso (derivedBaseChangeMapPlus A sq.toCommSq) :=
    isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism A sq
  let c := (V.mapDerivedCategoryPlusSingleFunctor 0).app F ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso ((constantAbelianPullbackIso a).app M)
  let e := (U.mapDerivedCategoryPlusHomologyFunctorIso q).app
      ((lowerStar A h).rightDerivedFunctorPlus.obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((derivedBaseChangeMapPlus A sq.toCommSq).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((lowerStar A h').rightDerivedFunctorPlus.mapIso c)
  exact IsZero.of_full_of_faithful_of_isZero U _ (hz.of_iso e)

end AlgebraicGeometry.Etale

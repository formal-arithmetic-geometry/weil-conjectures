/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Filtered colimits of abelian higher direct images

Source: Stacks Project, Tag 073E, via the integral coefficient comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem integralForget_equivalence (X : Scheme.{u}) :
    (moduleAbelianForget (ULift.{u + 1} ℤ) X).IsEquivalence := by
  let U := ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := U.asEquivalence
  let S := sheafCompose X.smallEtaleTopology U
  have : S.EssSurj := ⟨fun P ↦ by
    let Q := (sheafCompose X.smallEtaleTopology e.inverse).obj P
    refine ⟨Q, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj e.counitIso)⟩
  have : S.IsEquivalence := {}
  exact this

private noncomputable def higherDirectImageForgetIso
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) :
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ q) ⋙
      moduleAbelianForget (ULift.{u + 1} ℤ) X ≅
    moduleAbelianForget (ULift.{u + 1} ℤ) Y ⋙
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q) :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (moduleAbelianForget (ULift.{u + 1} ℤ) X |>.mapDerivedCategoryPlusHomologyFunctorIso q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleAbelianDerivedLowerStarIso (ULift.{u + 1} ℤ) h)
      (DerivedCategory.Plus.homologyFunctor _ q) ≪≫ Functor.associator _ _ _) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (moduleAbelianForget (ULift.{u + 1} ℤ) Y |>.mapDerivedCategoryPlusSingleFunctor 0)
    ((lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ q) ≪≫
  Functor.associator _ _ _

/-- The higher direct image of abelian sheaves along a qcqs morphism preserves filtered
colimits. Source: Stacks Project, Tag 073E
(blueprint: lem-kun-abelian-higher-direct-image-filtered-colimit).

Proof: integral coefficient forgetting is an equivalence on sheaves. The canonical
single-complex, derived direct-image and homology comparisons identify the integral
higher direct image followed by forgetting with forgetting followed by the abelian
higher direct image. The integral higher direct image preserves filtered colimits.
Transport that assertion across the two equivalences. -/
theorem preservesColimitsOfShape_abelianHigherDirectImage
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ q) := by
  let U := moduleAbelianForget (ULift.{u + 1} ℤ) Y
  let V := moduleAbelianForget (ULift.{u + 1} ℤ) X
  let H := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q
  have : U.IsEquivalence := integralForget_equivalence Y
  have : V.IsEquivalence := integralForget_equivalence X
  have := preservesColimitsOfShape_higherDirectImage (ULift.{u + 1} ℤ) h q J
  have : PreservesColimitsOfShape J (U ⋙ H) :=
    preservesColimitsOfShape_of_natIso (higherDirectImageForgetIso h q)
  have : PreservesColimitsOfShape J (U.inv ⋙ U ⋙ H) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    ((Functor.associator U.inv U H).symm ≪≫
      Functor.isoWhiskerRight U.asEquivalence.counitIso H ≪≫ Functor.leftUnitor H)

end AlgebraicGeometry.Etale

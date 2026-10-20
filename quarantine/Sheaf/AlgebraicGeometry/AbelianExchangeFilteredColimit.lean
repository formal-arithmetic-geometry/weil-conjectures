/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageFilteredColimit
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Filtered-colimit passage for exchange
Source: Stacks Project, Tags 073E and 0F1I.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private noncomputable def unboundedHigherDirectImageIso
    {X Y : Scheme.{u}} (g : Y ⟶ X) (q : ℤ) :
    DerivedCategory.singleFunctor _ 0 ⋙
      (lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q ≅
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (lowerStar AddCommGrpCat.{u + 1} g |>.rightDerivedFunctorPlusCompatibility).symm ≪≫
        (Functor.associator _ _ _).symm) _ ≪≫ Functor.associator _ _ _

private theorem preservesColimitsOfShape_unboundedHigherDirectImage
    {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g] [QuasiSeparated g]
    (q : ℤ) (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (DerivedCategory.singleFunctor _ 0 ⋙
      (lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q) := by
  have := preservesColimitsOfShape_abelianHigherDirectImage g q J
  exact preservesColimitsOfShape_of_natIso (unboundedHigherDirectImageIso g q).symm

private theorem exchangeSource_preserves
    {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (q : ℤ) (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (DerivedCategory.singleFunctor _ 0 ⋙
      ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor ⋙
        (upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory) ⋙
      DerivedCategory.homologyFunctor _ q) := by
  have := preservesColimitsOfShape_unboundedHigherDirectImage g q J
  let U := upperStar AddCommGrpCat.{u + 1} p
  let Rg := (lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  have : PreservesColimitsOfShape J ((DerivedCategory.singleFunctor _ 0 ⋙ Rg ⋙ H) ⋙ U) :=
    inferInstance
  apply preservesColimitsOfShape_of_natIso (F :=
    (DerivedCategory.singleFunctor _ 0 ⋙ Rg ⋙ H) ⋙ U)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (U.mapDerivedCategoryHomologyFunctorIso q) ≪≫
      (Functor.associator _ _ _).symm)

private theorem exchangeTarget_preserves
    {X T Y : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (DerivedCategory.singleFunctor _ 0 ⋙
      ((upperStar AddCommGrpCat.{u + 1} e).mapDerivedCategory ⋙
        (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctor) ⋙
      DerivedCategory.homologyFunctor _ q) := by
  have := preservesColimitsOfShape_unboundedHigherDirectImage h q J
  let V := upperStar AddCommGrpCat.{u + 1} e
  let Rh := (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  have : PreservesColimitsOfShape J (V ⋙ DerivedCategory.singleFunctor _ 0 ⋙ Rh ⋙ H) :=
    inferInstance
  apply preservesColimitsOfShape_of_natIso (F :=
    V ⋙ DerivedCategory.singleFunctor _ 0 ⋙ Rh ⋙ H)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (V.mapDerivedCategorySingleFunctor 0).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm

private theorem isIso_natTrans_app_colimit
    {J : Type} [SmallCategory J] {C D : Type (u + 2)}
    [Category.{u + 1} C] [Category.{u + 1} D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    {U V : C ⥤ D} (η : U ⟶ V) (M : J ⥤ C)
    [PreservesColimitsOfShape J U] [PreservesColimitsOfShape J V]
    (h : ∀ j, IsIso (η.app (M.obj j))) : IsIso (η.app (colimit M)) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft M η).app j) := h
  have : IsIso (Functor.whiskerLeft M η) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit M η
    (colimit.cocone M) (colimit.isColimit M)

/-- A filtered colimit of sheaves on which exchange is invertible again has invertible
exchange. Source: Stacks Project, Tag 073E
(blueprint: lem-kun-abelian-exchange-filtered-colimit).

Proof: Apply homology in each integer degree to the natural exchange transformation
on sheaves in degree zero. Exact inverse image commutes with homology and colimits,
and qcqs higher direct image commutes with filtered colimits. Thus both endpoint
functors preserve this colimit. Naturality identifies its exchange with the colimit
of the component exchanges, which is invertible. Cohomology detects invertibility. -/
theorem isIso_exactExchange_colimit
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g]
    (J : Type) [SmallCategory J] [IsFiltered J]
    (M : J ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : ∀ j, IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      sq.toCommSq).app ((DerivedCategory.singleFunctor _ 0).obj (M.obj j)))) :
    IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.singleFunctor _ 0).obj (colimit M))) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq inferInstance
  apply (DerivedCategory.isIso_iff _ _).mpr
  intro q
  have := exchangeSource_preserves p g q J
  have := exchangeTarget_preserves e h q J
  let η := Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
    (Functor.whiskerRight (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)
      (DerivedCategory.homologyFunctor _ q))
  exact isIso_natTrans_app_colimit η M (fun j ↦ by
    have := hM j
    change IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.singleFunctor _ 0).obj (M.obj j))))
    infer_instance)

end AlgebraicGeometry.Etale

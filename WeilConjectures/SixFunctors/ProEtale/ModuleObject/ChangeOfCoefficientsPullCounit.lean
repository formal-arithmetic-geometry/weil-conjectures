/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsCompCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac

/-!

# (Pull) on the image of the homotopy category

The derived (Pull) `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso` is, modulo the
counits of the left derived functors, the underived (Pull) `ProEtale.CondensedRing.pullIso`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso_hom_app_comp_counit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)



/-- `ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory` is compatible with the
counit of `Lf^*`. -/
@[reassoc]
lemma leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv.app (DerivedCategory.Qh.obj K) ≫
        ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K =
      ((f)^*⟦Λ⟧).mapDerivedCategoryFactorsh.hom.app K :=
  Functor.leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_counit _ K

/-- The underived (Pull) `pullIso` and `mapModUpperStarExtendScalarsIso` on the homotopy
categories. -/
lemma mapHomotopyCategoryCompIso_extendScalarsComp_comp_mapModUpperStarExtendScalarsIso
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).symm
          (ComplexShape.up ℤ)).hom.app
        ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (mapModUpperStarExtendScalarsIso a f).hom
        (ComplexShape.up ℤ)).app K =
    (NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.mapHomotopyCategory_app]
  have hcI : (Functor.mapHomotopyCategoryCompIso
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).symm
          (ComplexShape.up ℤ)).hom.app
        ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) =
      (HomotopyCategory.quotient _ _).map ((Functor.mapHomologicalComplexCompIso
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).symm
          (ComplexShape.up ℤ)).hom.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex _ |>.obj P)) := rfl
  rw [hcI, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [mapModUpperStarExtendScalarsIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, Mod.comp_hom',
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  rw [← Category.assoc, ← Mod.comp_hom']
  erw [Iso.inv_hom_id_app]
  erw [Mod.id_hom', Category.id_comp, Category.id_comp]

set_option profiler true in
/-- **(Pull) is the underived (Pull) modulo the counits**: on the image `Qh K` of an object of the
homotopy category, `derivedUpperStarExtendScalarsIso a f` followed by the counits of `L(Ext_{a_Y})`
and `Lf^*_Λ'` is the counit of `Lf^*_Λ`, followed by the counit of `L(Ext_{a_X})` and the
underived (Pull) `pullIso a f`. -/
lemma derivedUpperStarExtendScalarsIso_hom_app_comp_counit
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    (derivedUpperStarExtendScalarsIso a f).hom.app (DerivedCategory.Qh.obj K) ≫
        L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
        ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app K) =
      (L(Mod.extendScalars (coefficientMap a X)).map (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K) ≫
        (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
          ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
            (ComplexShape.up ℤ)).hom.app K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K) :
        (L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X))).obj
          (DerivedCategory.Qh.obj K) ⟶ _) := by
  have hPull : (pullIsoHomotopy a f).app K =
      (NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [pullIsoHomotopy, Functor.mapHomotopyCategoryCommIsoHom, NatTrans.comp_app,
      Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj,
      Functor.mapHomotopyCategoryCompIso_inv_app_quotient_obj, ← Functor.map_comp]
    refine congrArg _ ?_
    ext n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
      NatTrans.id_app, Category.comp_id]
  simpa only [DerivedUpperStarExtendScalarsIsoFac, hPull,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, DerivedCategory.Qh.map_id,
    Category.comp_id, Category.id_comp] using derivedUpperStarExtendScalarsIsoFac a f K

end AlgebraicGeometry.ProEtale.CondensedRing

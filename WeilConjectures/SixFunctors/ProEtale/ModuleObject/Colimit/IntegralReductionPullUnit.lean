/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural

/-!

# (Pull) is compatible with the units of the extension-restriction adjunctions

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. Write `η` for the units of the derived adjunctions `L(Ext_{a_Z}) ⊣ D(Res_{a_Z})`,
`ι : D(Res_{a_Y}) ⋙ Lf^*_Λ ≅ Lf^*_Λ' ⋙ D(Res_{a_X})` for the commutation of the restriction of
scalars with the derived pullbacks (`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`)
and (Pull) for `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a f`. This file proves
that (Pull) is compatible with the units: `Lf^*(η_M) ≫ ι = η_{Lf^* M} ≫ Res((Pull)_M)` for every
`M` (`upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app`).

On the image `Qh P` of a K-flat complex `P`, (Pull) and `ι` are computed, modulo the counits of
the left derived functors, by their underived counterparts
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso_hom_app_comp_counit`,
`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp`), and the units
by the levelwise units (`Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac`); the
statement then reduces to the compatibility of the underived (Pull) with the units
(`ProEtale.CondensedRing.upperStar_map_unit_comp_comapUpperStarIso_inv_app`). Every object of
the derived category being isomorphic to the image of a K-flat complex, this proves it in general.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Comap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The commutation `derivedComapLeftDerivedUpperStarIso` is obtained from the levelwise
commutation `derivedComapUpperStarIso` and the identifications of the derived pullbacks with the
levelwise pullbacks. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_eq :
    (derivedComapLeftDerivedUpperStarIso a f).hom =
      (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ f) ≪≫
        (derivedComapUpperStarIso a f).symm ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm _).hom := by
  ext K
  rw [derivedComapLeftDerivedUpperStarIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    derivedComapUpperStarIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategorySquareIso]
  rfl

set_option maxHeartbeats 4000000 in -- large composites of derived functors on sheaf categories

/-- The commutation `ι` of the restriction of scalars with the derived pullbacks, on the image of
an object of the homotopy category, is the underived commutation `comapUpperStarIso` modulo
the counits. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp
    (Z : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))
      (ComplexShape.up ℤ)) :
    (derivedComapLeftDerivedUpperStarIso a f).hom.app (DerivedCategory.Qh.obj Z) ≫
        D(Mod.comap (coefficientMap a X)).map (((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app Z) ≫
        (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.app
          ((((f)^*⟦Λ'⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X))) (ComplexShape.up ℤ)).hom.app Z) =
      (L((f)^*⟦Λ⟧).map ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app Z) ≫
        ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app
          (((Mod.comap (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧)) (ComplexShape.up ℤ)).hom.app Z) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (comapUpperStarIso a f).inv (ComplexShape.up ℤ)).app Z) :
        (D(Mod.comap (coefficientMap a Y)) ⋙ L((f)^*⟦Λ⟧)).obj (DerivedCategory.Qh.obj Z) ⟶ _) := by
  rw [derivedComapLeftDerivedUpperStarIso_hom_eq]
  simp only [derivedComapUpperStarIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  have s1 := congrArg (D(Mod.comap (coefficientMap a X))).map
    (leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit f Λ' Z)
  have s2 := Functor.mapDerivedCategoryCompIso_fach (f)^*⟦Λ'⟧ (Mod.comap (coefficientMap a X)) Z
  have s3 := Functor.mapDerivedCategoryNatIso_inv_app_Qh_comp_factorsh (comapUpperStarIso a f) Z
  have s4 := Functor.mapDerivedCategoryCompIso_inv_app_Qh_comp_factorsh
    (Mod.comap (coefficientMap a Y)) (f)^*⟦Λ⟧ Z
  have s5 := (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom.naturality
    ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app Z)
  have s6 := Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_comp_factorsh (f)^*⟦Λ⟧
    (((Mod.comap (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z)
  simp only [Functor.map_comp] at s1
  dsimp only [Functor.comp_obj, Functor.comp_map] at s1 s2 s3 s4 s5 s6 ⊢
  rw [reassoc_of% s1, s2, s3, reassoc_of% s4]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at s5 ⊢
  rw [← reassoc_of% s5, reassoc_of% s6]


/-- The underived compatibility of (Pull) with the units of `Ext ⊣ Res`
(`ProEtale.CondensedRing.upperStar_map_unit_comp_comapUpperStarIso_inv_app`), on the homotopy
categories. -/
lemma upperStar_mapHomotopyCategory_unit_comp_comapUpperStarIso_inv
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (ComplexShape.up ℤ)) :
    ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧))
          (ComplexShape.up ℤ)).hom.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (comapUpperStarIso a f).inv (ComplexShape.up ℤ)).app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X)))
          (ComplexShape.up ℤ)).inv.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
            (ComplexShape.up ℤ)).hom.app K) =
    ((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
            (ComplexShape.up ℤ)).hom.app K) ≫
      ((Mod.comap (coefficientMap a X)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K) := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 2
  have h := congrArg (fun g ↦ g.hom) (upperStar_map_unit_comp_comapUpperStarIso_inv_app a f (P.X n))
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
    Mod.comp_hom']
  simp only [Mod.comp_hom'] at h
  exact h

set_option maxHeartbeats 4000000 in -- large composites of derived functors on sheaf categories
/-- **(Pull) is compatible with the units of `Ext ⊣ Res`**, on the image of a K-flat complex. -/
lemma upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app_Qh
    (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    L((f)^*⟦Λ⟧).map ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app
        (L((f)^*⟦Λ⟧).obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedUpperStarExtendScalarsIso a f).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) := by
  set K := (HomotopyCategory.quotient
    (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ)).obj P
  have := (Mod.extendScalars (coefficientMap a Y)).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  have : IsIso ((f)^*⟦Λ'⟧.leftDerivedFunctorCounit) := inferInstance
  have i1 : IsIso (L((f)^*⟦Λ'⟧).map
      ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)) := inferInstance
  have i2 : IsIso (((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
      (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    inferInstance
  have i3 : IsIso (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
        (ComplexShape.up ℤ)).hom.app K)) := inferInstance
  have i4 : IsIso (L((f)^*⟦Λ'⟧).map
      ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
      ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
          (ComplexShape.up ℤ)).hom.app K)) := inferInstance
  refine (cancel_mono (D(Mod.comap (coefficientMap a X)).map
    (L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
      ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
        (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
          (ComplexShape.up ℤ)).hom.app K)))).1 ?_
  refine (cancel_mono ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.app
      (((Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K))).1 ?_
  have r1 := derivedUpperStarExtendScalarsIso_hom_app_comp_counit a f K
  have r2 := (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.naturality
    (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K)
  have r3 := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac (coefficientMap a X)
    ((((f)^*⟦Λ⟧).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have r4 := (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)))
        (ComplexShape.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory (pullIso a f).hom (ComplexShape.up ℤ)).app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at r1 r2 r3 r4 ⊢
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, r1]
  simp only [Functor.map_comp, Category.assoc] at r4 ⊢
  rw [← reassoc_of% r2, r4, reassoc_of% r3]
  have l1 := (derivedComapLeftDerivedUpperStarIso a f).hom.naturality
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)
  have l2 := (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧))
        (ComplexShape.up ℤ)).hom.app K)
  have i1 := derivedComapLeftDerivedUpperStarIso_hom_app_Qh_comp a f
    (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have i1' := i1 =≫ DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
    (Iso.refl ((f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X))) (ComplexShape.up ℤ)).inv.app
      (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
  simp only [Category.assoc, ← DerivedCategory.Qh.map_comp, Iso.hom_inv_id_app] at i1'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at i1'
  dsimp only [Functor.comp_obj, Functor.comp_map] at l1 l2 i1'
  rw [← reassoc_of% l1, l2, reassoc_of% i1']
  have r5 := Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac (coefficientMap a Y) K
  have e1 := ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.naturality
    (((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
      (ComplexShape.up ℤ)).unit.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at e1
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, r5, reassoc_of% e1]
  simp only [← DerivedCategory.Qh.map_comp, Category.assoc]
  rw [upperStar_mapHomotopyCategory_unit_comp_comapUpperStarIso_inv]

set_option maxHeartbeats 4000000 in -- large composites of derived functors on sheaf categories
/-- **(Pull) is compatible with the units of `Ext ⊣ Res`**: for `M ∈ D(Y_proét, Λ)`, the
pullback of the unit `M ⟶ Res (Ext M)`, followed by the commutation `ι` of `Res` with `Lf^*`, is
the unit at `Lf^* M` followed by `Res` of (Pull). -/
theorem upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).unit.app
        M) ≫
      (derivedComapLeftDerivedUpperStarIso a f).hom.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj M) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app
        (L((f)^*⟦Λ⟧).obj M) ≫
      D(Mod.comap (coefficientMap a X)).map ((derivedUpperStarExtendScalarsIso a f).hom.app M) := by
  let P := (CochainComplex.flatResolutionFunctor _).obj (DerivedCategory.Q.objPreimage M)
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) ≅ M :=
    (DerivedCategory.quotientCompQhIso _).app P ≪≫
      asIso (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app _)) ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have h := upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app_Qh a f P
    (CochainComplex.kFlat_flatResolutionFunctor_obj _)
  have n1 := (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).unit.naturality
    e.hom
  have n2 := (derivedComapLeftDerivedUpperStarIso a f).hom.naturality
    (L(Mod.extendScalars (coefficientMap a Y)).map e.hom)
  have n3 := (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.naturality
    (L((f)^*⟦Λ⟧).map e.hom)
  have n4 := (derivedUpperStarExtendScalarsIso a f).hom.naturality e.hom
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n1 n2 n3 n4
  rw [← cancel_epi (L((f)^*⟦Λ⟧).map e.hom), ← Functor.map_comp_assoc, n1, Functor.map_comp,
    Category.assoc, n2, reassoc_of% h, reassoc_of% n3, ← Functor.map_comp, ← Functor.map_comp,
    n4]

end Comap

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarCompNormalization
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompNatIsoCounit

/-! The one-arrow derived scalar pullback mate normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (a : A ⟶ B) [IsMonHom a]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.derivedExtendMapDerivedCategoryAdjunction

private theorem derived_unique_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    {q : C ⥤ D} {F : C ⥤ E} (W : MorphismProperty C) [q.IsLocalization W]
    (LF LF' : D ⥤ E) (c : q ⋙ LF ⟶ F) (c' : q ⋙ LF' ⟶ F)
    [LF.IsLeftDerivedFunctor c W] [LF'.IsLeftDerivedFunctor c' W] (K : C) :
    (Functor.leftDerivedUnique LF' LF c c' W).hom.app (q.obj K) ≫ c'.app K = c.app K := by
  simpa only [Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
    Functor.leftDerivedNatTrans_app LF LF' c c' W (𝟙 _) K

set_option profiler true in
set_option maxHeartbeats 2000000 in
-- Comparing the internal module-object derived functors needs this elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
/-- The specified nonflat derived scalar pullback comparison has the specified restriction mate.

Source: proof step 2 of `lem-sp-original-integral-finite-quotient-mate-transport`, above
`def-exchange-projection` in the latest blueprint.

Proof in words. Apply the existing derived mate/counit theorem to the underived identity
`mateEquiv_pullIso_hom`. The scalar adjunction counits have the required normalization
on Qh. For the left comparison, expand the chosen construction of the derived scalar
pullback isomorphism. Derived natural-transformation counit compatibility handles its
underived comparison factor, and uniqueness of left derived functors handles its two
exact composition factors. Naturality moves scalar transitivity to the complex input.
Factor the underived comparison into scalar transitivity and pullIso, apply
`scalarCompNormalization`, and cancel transitivity with its inverse. The last factor is
the counit equation for `leftDerivedUpperStarIso`. This one-arrow calculation has no
properness, constructibility, or nonzero-ring hypothesis.
(blueprint: lem-sp-derived-upper-star-extend-scalars-mate-normalization) -/
theorem derivedUpperStarExtendScalarsMateNormalization {U V : Scheme.{u}} (h : U ⟶ V) :
    mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
      (TwoSquare.mk _ _ _ _ (derivedUpperStarExtendScalarsIso a h).hom) =
      (derivedComapLeftDerivedUpperStarIso a h).hom := by
  let β := (pullIso a h).symm
  let e := (comapUpperStarIso a h).symm
  let Lβ := (derivedUpperStarExtendScalarsIso a h).symm
  let Γ := derivedComapLeftDerivedUpperStarIso a h
  refine Adjunction.mateEquiv_leftDerived_inv_eq
    (Mod.extendRestrictAdjunction (coefficientMap a V))
    (Mod.extendRestrictAdjunction (coefficientMap a U)) β e
    (mateEquiv_pullIso_hom a h)
    (Functor.mapHomotopyCategoryCompNatIso (pullIso a h) _).symm
    (Functor.mapHomotopyCategoryCompNatIso_hom (pullIso a h) _)
    _ _ _ _
    ((h)^*⟦A⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    _ _ ((h)^*⟦B⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq _)
    Lβ _ rfl _ rfl (fun K => ?_) Γ (by rfl)
  simp only [Lβ, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.mapHomotopyCategoryCompNatIso_hom,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  simp only [derivedUpperStarExtendScalarsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, Category.assoc]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory B h).inv.naturality
    ((Mod.extendScalars (coefficientMap a V)).leftDerivedFunctorCounit.app K)
  simp only [Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  have hB := (h)^*⟦B⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    (((Mod.extendScalars (coefficientMap a V)).mapHomotopyCategory (.up ℤ)).obj K)
  rw [← hB]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc]
  have hr := derived_unique_fac
    (HomotopyCategory.quasiIso _ (.up ℤ))
    L(Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧)
    (L(Mod.extendScalars (coefficientMap a V)) ⋙ D((h)^*⟦B⟧))
    (Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧).leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit _ _) K
  change (Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso
      (Mod.extendScalars (coefficientMap a V)) (h)^*⟦B⟧).hom.app
        (DerivedCategory.Qh.obj K) ≫
      (Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit _ _).app K = _ at hr
  simp only [Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Category.id_comp] at hr
  dsimp only [Functor.comp_obj] at hr
  change _ ≫ _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) = _ at hr
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hr
  erw [hr]
  have hi := Functor.leftDerivedNatTrans_app
    L((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U))
    L(Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧)
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U)).leftDerivedFunctorCounit
    (Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧).leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (mapModUpperStarExtendScalarsIso a h).hom (.up ℤ))
      DerivedCategory.Qh) K
  change (Functor.leftDerivedFunctorIsoOfIso (mapModUpperStarExtendScalarsIso a h)).hom.app
      (DerivedCategory.Qh.obj K) ≫ _ = _ at hi
  simp only [Functor.whiskerRight_app] at hi
  erw [hi]
  have := Functor.isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V))
    (Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U))
  have hl := derived_unique_fac (HomotopyCategory.quasiIso _ (.up ℤ))
    L((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U))
    (D((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)) ⋙
      L(Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U)))
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U)).leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryCounit _ _) K
  change (Functor.leftDerivedFunctorCompMapDerivedCategoryIso _ _).hom.app
    (DerivedCategory.Qh.obj K) ≫ _ = _ at hl
  rw [← hl]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.leftDerivedFunctorCompMapDerivedCategoryCounit,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := (Mod.derivedExtendScalarsCompIso (condensedPullbackHom A h)
    (coefficientMap a U) _ rfl).inv.naturality
      (((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapDerivedCategoryFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at ht
  rw [← reassoc_of% ht]
  have hm : (NatTrans.mapHomotopyCategory
      (mapModUpperStarExtendScalarsIso a h).hom (.up ℤ)).app K =
      (NatTrans.mapHomotopyCategory
        (Mod.extendScalarsComp (condensedPullbackHom A h) (coefficientMap a U)).hom
        (.up ℤ)).app
          ((((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapHomotopyCategory
            (.up ℤ)).obj K) ≫
        (NatTrans.mapHomotopyCategory (pullIso a h).hom (.up ℤ)).app K := by
    obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ =
      (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map _
    rw [← Functor.map_comp]
    congr 1
  rw [hm, Functor.map_comp]
  have hs := scalarCompNormalization (condensedPullbackHom A h) (coefficientMap a U)
    ((((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapHomotopyCategory (.up ℤ)).obj K)
  simp only [Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.comp_id] at hs
  have hs' := congrArg (fun m =>
    (Mod.derivedExtendScalarsCompIso (condensedPullbackHom A h)
      (coefficientMap a U) _ rfl).inv.app
        (DerivedCategory.Qh.obj
          ((((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapHomotopyCategory
            (.up ℤ)).obj K)) ≫ m) hs
  simp only [Iso.inv_hom_id_app_assoc] at hs'
  rw [← reassoc_of% hs']
  have := Functor.isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V))
    (Mod.extendScalars (condensedPullbackHom A h))
  have hA := derived_unique_fac (HomotopyCategory.quasiIso _ (.up ℤ))
    L((h)^*⟦A⟧)
    (D((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)) ⋙
      L(Mod.extendScalars (condensedPullbackHom A h)))
    (h)^*⟦A⟧.leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryCounit _ _) K
  change (leftDerivedUpperStarIso A h).hom.app (DerivedCategory.Qh.obj K) ≫ _ = _ at hA
  simp only [Functor.leftDerivedFunctorCompMapDerivedCategoryCounit,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hA
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hA
  simp only [← Functor.map_comp_assoc]
  erw [hA]
  rfl


end AlgebraicGeometry.ProEtale.CondensedRing

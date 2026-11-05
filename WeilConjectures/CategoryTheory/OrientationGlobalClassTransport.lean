/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import all WeilConjectures.CategoryTheory.RightDerivedBaseChangeSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.HomotopyCategory
import all Mathlib.CategoryTheory.Shift.InducedShiftSequence
import all WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalRealizationShift

/-! # Normalization of section transport

Source: Stacks Tag 05TD, the derived augmentation equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' d
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasDerivedCategory.{w'} C']
  [EnoughInjectives C] [EnoughInjectives C']
  {D : Type d} [Category D] [Abelian D] [HasDerivedCategory D]

/-- Derived transport with the derived identity comparison removed.
Source: Stacks Tag 05TD (blueprint: lem-pur-orientation-global-class-transport). -/
def orientationGlobalClassTransport
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E') :
    E.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ E'.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso D)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := E) (G' := E') (β := L) (γ := 𝟭 D) ((Functor.rightUnitor _).hom ≫ τ)

private theorem coordinate_id_shift :
    NatTrans.CommShift (Functor.mapDerivedCategoryPlusIdIso D).hom ℤ := by
  have hh : whiskerRight (mapDerivedCategoryPlusIdIso D).hom DerivedCategory.Plus.ι =
      (𝟭 D).mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryIdIso D).hom ≫
        DerivedCategory.Plus.ι.rightUnitor.hom ≫ DerivedCategory.Plus.ι.leftUnitor.inv := by
    ext K
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id]
    erw [ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    simp only [mapDerivedCategoryPlusCompatibility,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    exact (Category.comp_id _).symm
  have := AlgebraicGeometry.ProEtale.exactCompatibility_shift (𝟭 D)
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusIdIso D).hom DerivedCategory.Plus.ι) ℤ := by
    rw [hh]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

/-- Normalized section transport respects shifts.
Source: Stacks Tag 05TD.
Proof: the identity comparison respects shifts after the faithful bounded-below
inclusion, where it is the proved unbounded identity comparison. Its inverse,
whiskering and composition with the base-change transformation preserve this property.
(blueprint: lem-pur-orientation-global-class-transport). -/
theorem orientationGlobalClassTransport_shift
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E') :
    NatTrans.CommShift (orientationGlobalClassTransport L E E' τ) ℤ := by
  have := coordinate_id_shift (D := D)
  have : NatTrans.CommShift (CategoryTheory.inv (mapDerivedCategoryPlusIdIso D).hom) ℤ :=
    NatTrans.CommShift.of_isIso (mapDerivedCategoryPlusIdIso D).hom ℤ
  have : NatTrans.CommShift (mapDerivedCategoryPlusIdIso D).inv ℤ := by
    have he : CategoryTheory.inv (mapDerivedCategoryPlusIdIso D).hom =
        (mapDerivedCategoryPlusIdIso D).inv :=
      IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id _)
    rw [he] at this
    exact this
  unfold orientationGlobalClassTransport
  simp only [Functor.isoWhiskerLeft_inv]
  infer_instance

private theorem coordinate_id_single (Y : D) :
    ((𝟭 D).mapDerivedCategoryPlusSingleFunctor 0).hom.app Y =
      (mapDerivedCategoryPlusIdIso D).hom.app
        ((DerivedCategory.Plus.singleFunctor D 0).obj Y) := by
  have ht := single_exact_transport (𝟭 D) Y
  simp only [singleTransport_hom, Functor.map_id, Category.id_comp,
    Category.comp_id] at ht
  have hi : (homotopySingleIso (𝟭 D) Y).hom = 𝟙 _ := by
    apply (HomotopyCategory.Plus.ι D).map_injective
    simp only [homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
      Functor.mapIso_hom]
    have hs : (HomologicalComplex.singleMapHomologicalComplex (𝟭 D)
        (ComplexShape.up ℤ) 0).hom.app Y = 𝟙 _ := by
      ext n
      by_cases hn : n = 0
      · subst n
        simp
      · exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 Y n hn).eq_of_src _ _
    change (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex (𝟭 D)
        (ComplexShape.up ℤ) 0).hom.app Y) = _
    erw [hs, Functor.map_id]
  erw [hi, Functor.map_id, Category.comp_id] at ht
  erw [ht, ← mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  rfl

/-- The normalized transport carries the derived augmentation to the target augmentation.
Source: Stacks Tag 05TD.
Proof: the unnormalized single-complex equation is `rightDerivedBaseChange_single_unit`.
Move the inverse identity comparison across the source augmentation by naturality.
Its value on a single object is the exact identity single comparison, so these
comparisons cancel. This proves the equation before taking any homology.
(blueprint: lem-pur-orientation-global-class-transport). -/
theorem orientationGlobalClassTransport_single_unit
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E')
    (Y : C) :
    E.rightDerivedPlusSingleUnit Y ≫
        (orientationGlobalClassTransport L E E' τ).app
          ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
        E'.rightDerivedFunctorPlus.map ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y) =
      (DerivedCategory.Plus.singleFunctor D 0).map (τ.app Y) ≫
        E'.rightDerivedPlusSingleUnit (L.obj Y) := by
  have hh := rightDerivedBaseChange_single_unit
    (G := E) (G' := E') (β := L) (γ := 𝟭 D) ((Functor.rightUnitor E).hom ≫ τ) Y
  have hn := (mapDerivedCategoryPlusIdIso D).inv.naturality (E.rightDerivedPlusSingleUnit Y)
  simp only [Functor.id_map] at hn
  unfold orientationGlobalClassTransport
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app,
    isoWhiskerLeft_inv, whiskerLeft_app, Category.id_comp, Category.assoc]
  erw [reassoc_of% hn, hh, coordinate_id_single,
    Iso.inv_hom_id_app_assoc]
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app]
  erw [Category.id_comp]

/-- Degree-zero homology of normalized section transport respects the augmentations.
Source: Stacks Tag 05TD.
Proof: take H0 of the preceding single-complex equation. The single/H0 isomorphism
is natural in the underived map. The proved single-unit homology comparison
identifies both augmentations with their classical degree-zero versions.
(blueprint: lem-pur-orientation-global-class-transport). -/
theorem orientationGlobalClassTransport_zero_unit
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E')
    (Y : C) :
    E.toRightDerivedZero.app Y ≫
        (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).inv ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((orientationGlobalClassTransport L E E' τ).app
            ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≫
              E'.rightDerivedFunctorPlus.map
                ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y)) =
      τ.app Y ≫ E'.toRightDerivedZero.app (L.obj Y) ≫
        (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).inv := by
  have hu := congrArg (fun z ↦ z ≫
      (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).inv)
    (rightDerivedPlusSingleUnitHomology_comp_comparison E Y)
  have hu' := congrArg (fun z ↦ z ≫
      (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).inv)
    (rightDerivedPlusSingleUnitHomology_comp_comparison E' (L.obj Y))
  change (E.rightDerivedPlusSingleUnitHomology Y ≫
      (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).hom) ≫
      (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y 0).inv = _ at hu
  change (E'.rightDerivedPlusSingleUnitHomology (L.obj Y) ≫
      (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).hom) ≫
      (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj Y) 0).inv = _ at hu'
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hu hu'
  let H := DerivedCategory.Plus.homologyFunctor D 0
  have hn := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := D) 0).inv.naturality (τ.app Y)
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← Category.assoc, ← hu, ← hu']
  unfold rightDerivedPlusSingleUnitHomology
  simp only [Functor.map_comp, Category.assoc]
  erw [← H.map_comp_assoc, ← H.map_comp]
  simp only [Category.assoc]
  erw [orientationGlobalClassTransport_single_unit, H.map_comp, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  rfl

end CategoryTheory.Functor

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate

/-! # Right path of the normalized mixed Leray unit diagram
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-right-unit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
-- Scalar restriction expands exact-functor localization instances.
private theorem scalar_factor
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (.up ℤ)) :
    let Sf := ModuleCat.restrictScalars.{u} f.appTop.hom
    let Sg := ModuleCat.restrictScalars.{u} g.appTop.hom
    let Sfg := ModuleCat.restrictScalars.{u} (f ≫ g).appTop.hom
    Sfg.mapDerivedCategoryFactorsh.inv.app K ≫
      (schemeGlobalScalarRestrictionCompIso f g).hom.app (DerivedCategory.Qh.obj K) =
    Sg.mapDerivedCategoryFactorsh.inv.app ((Sf.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeGlobalScalarRestriction g).map (Sf.mapDerivedCategoryFactorsh.inv.app K) := by
  let Sf := ModuleCat.restrictScalars.{u} f.appTop.hom
  let Sg := ModuleCat.restrictScalars.{u} g.appTop.hom
  let Sfg := ModuleCat.restrictScalars.{u} (f ≫ g).appTop.hom
  let e₀ := ModuleCat.restrictScalarsComp' g.appTop.hom f.appTop.hom
    (f ≫ g).appTop.hom rfl
  have h₀ : (NatTrans.mapHomotopyCategory e₀.hom (.up ℤ)).app K = 𝟙 _ := by
    obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ = 𝟙 _
    rw [← CategoryTheory.Functor.map_id]
    congr 1
  have hn := Functor.mapDerivedCategoryNatIso_fach e₀ K
  erw [h₀, CategoryTheory.Functor.map_id, Category.comp_id] at hn
  have hc := Functor.mapDerivedCategoryCompIso_fach Sf Sg K
  erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    CategoryTheory.Functor.map_id, Category.comp_id] at hc
  dsimp only [schemeGlobalScalarRestrictionCompIso, Iso.trans_hom, NatTrans.comp_app]
  apply (cancel_mono (Sg.mapDerivedCategory.map (Sf.mapDerivedCategoryFactorsh.hom.app K) ≫
    Sg.mapDerivedCategoryFactorsh.hom.app ((Sf.mapHomotopyCategory (.up ℤ)).obj K))).1
  simp only [Category.assoc]
  erw [hc, hn]
  change Sfg.mapDerivedCategoryFactorsh.inv.app K ≫
      Sfg.mapDerivedCategoryFactorsh.hom.app K =
    Sg.mapDerivedCategoryFactorsh.inv.app ((Sf.mapHomotopyCategory (.up ℤ)).obj K) ≫
      Sg.mapDerivedCategory.map (Sf.mapDerivedCategoryFactorsh.inv.app K) ≫
      Sg.mapDerivedCategory.map (Sf.mapDerivedCategoryFactorsh.hom.app K) ≫
      Sg.mapDerivedCategoryFactorsh.hom.app ((Sf.mapHomotopyCategory (.up ℤ)).obj K)
  erw [Iso.inv_hom_id_app, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]
  rfl

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

set_option maxHeartbeats 800000 in
-- The chosen comparison expands sheaf and localization instances.
private theorem mixed_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let H := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let S := ModuleCat.restrictScalars.{u} f.appTop.hom
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
        ((D.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeDerivedGlobalSections Y).map (D.rightDerivedFunctorUnit.app K) ≫
      (mixedGlobalSectionsDirectImageIso f).hom.app (DerivedCategory.Qh.obj K) =
    S.mapDerivedCategoryFactorsh.inv.app ((H.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeGlobalScalarRestriction f).map (H.rightDerivedFunctorUnit.app K) := by
  let c₀ := Classical.choose (exists_mixedGlobalSectionsDirectImageIso f)
  have h₀ := (Classical.choose_spec (Classical.choose_spec
    (exists_mixedGlobalSectionsDirectImageIso f))).1
  have hc := (Classical.choose_spec (Classical.choose_spec
    (exists_mixedGlobalSectionsDirectImageIso f))).2 K
  have he : c₀ = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext x
    exact h₀ M x
  dsimp only [c₀] at he
  conv at hc => rhs; rw [he]
  simp only [Iso.refl_symm] at hc
  erw [Iso.hom_inv_id_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hc
  simpa only [mixedGlobalSectionsDirectImageIso, CategoryTheory.Functor.map_id,
    Category.id_comp] using hc

set_option maxHeartbeats 400000 in
-- The statement expands sheaf, scalar, and localization instances.
/-- The right path becomes the iterated scalar-factor path before any unit cancellation.
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W; the pinned-unit calculation
in lem-sc-mixed-sections-composition-kinjective.
(blueprint: lem-sc-mixed-sections-right-unit-normalization).

Proof: Distribute derived global sections over the final two direct-image maps in p.
The factors e.inv and e.hom cancel because e is an isomorphism. The mixed Leray
unit equation for f followed by g identifies the remaining path with the
composite scalar factor followed by Sfg(unit_HX). Naturality of the scalar
composition comparison moves unit_HX to the end. The factor identity identifies
factor_fg followed by s(f,g) with factor_g followed by Sg(factor_f). This follows
from mapDerivedCategoryCompIso_fach and mapDerivedCategoryNatIso_fach, applied to
restrictScalarsComp'. On each degree the underived comparison is the identity
on elements, so its homotopy map and its localization map are identities.
Thus this path is b. No acyclicity or K-injectivity assumption is needed.
For identity maps, zero complexes, and empty schemes the same equations hold;
no nonemptiness, boundedness, flatness, or preservation of K-injectivity is used.
The sheaf and module localization universes remain independent. -/
theorem mixedSections_right_unit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
    let F := DerivedCategory.Qh.obj K
    let Df := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let Dfg := RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom
    let HX := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let HY := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let HZ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
    let Sf := ModuleCat.restrictScalars.{u}
      (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom
    let Sg := ModuleCat.restrictScalars.{u}
      (R := (moduleRings Z.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings Y.toRingedSpace).obj.obj (op ⊤)) g.appTop.hom
    let e := schemeNormalizedDirectImageCompIso f g
    let p := HZ.rightDerivedFunctorUnit.app ((Dfg.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeDerivedGlobalSections Z).map (Dfg.rightDerivedFunctorUnit.app K) ≫
      (schemeDerivedGlobalSections Z).map (e.inv.app F)
    let b := Sg.mapDerivedCategoryFactorsh.inv.app
        ((HY.mapHomotopyCategory (.up ℤ)).obj ((Df.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        (Sf.mapDerivedCategoryFactorsh.inv.app ((HX.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalScalarRestriction f).map (HX.rightDerivedFunctorUnit.app K))
    p ≫ (schemeDerivedGlobalSections Z).map (e.hom.app F) ≫
      (mixedGlobalSectionsDirectImageIso (f ≫ g)).hom.app F ≫
      (schemeGlobalScalarRestrictionCompIso f g).hom.app
        ((schemeDerivedGlobalSections X).obj F) = b := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let F := DerivedCategory.Qh.obj K
  let HZ := schemeDerivedGlobalSections Z
  let e := schemeNormalizedDirectImageCompIso f g
  have he : HZ.map (e.inv.app F) ≫ HZ.map (e.hom.app F) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
  dsimp only
  simp only [Category.assoc]
  erw [reassoc_of% he]
  erw [reassoc_of% (mixed_unit (f ≫ g) K)]
  erw [(schemeGlobalScalarRestrictionCompIso f g).hom.naturality
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K)]
  rw [← Category.assoc]
  erw [scalar_factor f g
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory (.up ℤ)).obj K)]
  simp only [Category.assoc, CategoryTheory.Functor.comp_map]
  rfl

end AlgebraicGeometry

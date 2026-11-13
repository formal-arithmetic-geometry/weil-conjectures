/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyAugmentedLift

/-! # Restriction on the homology of fixed-resolution section complexes

## References

* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
* [Stacks Project, Tag 01E2](https://stacks.math.columbia.edu/tag/01E2)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- The section calculation crosses the scheme-module and ringed-space section interfaces.
/-- Restriction between arbitrary opens on the homology of a fixed resolution's
section complexes, before the map to a cohomology sheaf. -/
theorem restrictedResolution_open_cohomology {Z : Scheme.{u}} {F : Z.Modules}
    (I : InjectiveResolution F) (U L : Z.Opens) (e : L ≤ U)
    (R : RestrictedResolutionSections I U) (R' : RestrictedResolutionSections I L)
    (p : ℕ) :
    let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive L.toScheme.toRingedSpace
    let j := Z.homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app F ≪≫
      (restrictFunctorCongr (Z.homOfLE_ι e)).app F
    moduleCohomologyFMap j
      ((restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj F) ≫
        (pushforward j).map c.hom) p ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        (R'.resolution.isoRightDerivedObj
          (RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R'.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        R'.sections.hom =
    (forget₂ _ AddCommGrpCat.{u}).map
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      R.sections.hom ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
            PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
              ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
                (homOfLE e).op))
          (ComplexShape.up ℕ)).app I.cocomplex) := by
  let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let := RingedSpace.globalSectionsFunctor_additive L.toScheme.toRingedSpace
  let j := Z.homOfLE e
  let P := pushforward j
  let Q := restrictFunctor j
  let c := (restrictFunctorComp j U.ι).symm ≪≫
    restrictFunctorCongr (Z.homOfLE_ι e)
  let t := (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map R.comparison.hom ≫
    (NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℕ)).app I.cocomplex ≫
      R'.comparison.inv
  let β := (NatTrans.mapHomologicalComplex (restrictAdjunction j).unit
    (ComplexShape.up ℕ)).app R.resolution.cocomplex ≫
      (P.mapHomologicalComplex (ComplexShape.up ℕ)).map t
  let φ := (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj F) ≫
    P.map (c.hom.app F)
  have ht : Q.map (R.resolution.ι.f 0) ≫ t.f 0 =
      c.hom.app F ≫ R'.resolution.ι.f 0 := by
    dsimp only [t]
    simp only [HomologicalComplex.comp_f]
    change Q.map (R.resolution.ι.f 0) ≫ Q.map (R.comparison.hom.f 0) ≫
      c.hom.app (I.cocomplex.X 0) ≫ R'.comparison.inv.f 0 = _
    rw [← Category.assoc, ← Q.map_comp, R.augmentation]
    erw [← Category.assoc, c.hom.naturality (I.ι.f 0)]
    change c.hom.app F ≫ (restrictFunctor L.ι).map (I.ι.f 0) ≫
      R'.comparison.inv.f 0 = _
    rw [← R'.augmentation, Category.assoc]
    have hc : R'.comparison.hom.f 0 ≫ R'.comparison.inv.f 0 = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    rw [hc, Category.comp_id]
  have hβ : R.resolution.ι.f 0 ≫ β.f 0 = φ ≫ P.map (R'.resolution.ι.f 0) := by
    dsimp only [β]
    rw [HomologicalComplex.comp_f]
    change R.resolution.ι.f 0 ≫ (restrictAdjunction j).unit.app
      (R.resolution.cocomplex.X 0) ≫ P.map (t.f 0) = _
    erw [← Category.assoc, (restrictAdjunction j).unit.naturality
      (R.resolution.ι.f 0)]
    change (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj F) ≫
      P.map (Q.map (R.resolution.ι.f 0)) ≫ P.map (t.f 0) = _
    erw [← P.map_comp, ht, P.map_comp]
    rfl
  let Γ := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}
  let a : ((RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R'.resolution.cocomplex ≅
      (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R'.resolution.cocomplex) := by
    refine (HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (presheaf (R'.resolution.cocomplex.X n)).mapIso
        (eqToIso (by simp) : op (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) ≅
          op (⊤ : L.toScheme.Opens))) ?_).symm
    intro n m _
    exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (R'.resolution.cocomplex.d n m)).naturality _
  have ha : ∀ n : ℕ, a.inv.f n = (R'.resolution.cocomplex.X n).presheaf.map
      (eqToHom (by simp) : (⊤ : L.toScheme.Opens) ⟶
        j ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op := by intro n; rfl
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
      ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map (homOfLE e).op))
    (ComplexShape.up ℕ)).app I.cocomplex
  have hc : (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map β ≫
      a.inv ≫ R'.sections.hom = R.sections.hom ≫ r := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, R'.components, R.components]
    dsimp only [β, t, Γ, r]
    change Hom.app ((restrictAdjunction j).unit.app (R.resolution.cocomplex.X n)) ⊤ ≫
      Hom.app (Q.map (R.comparison.hom.f n) ≫ c.hom.app (I.cocomplex.X n) ≫
        R'.comparison.inv.f n) (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) ≫
      (R'.resolution.cocomplex.X n).presheaf.map _ ≫
      Hom.app (R'.comparison.hom.f n) ⊤ ≫
      (restrictAppIso L.ι (I.cocomplex.X n) ⊤).hom ≫
      (I.cocomplex.X n).presheaf.map _ =
      Hom.app (R.comparison.hom.f n) ⊤ ≫
      (restrictAppIso U.ι (I.cocomplex.X n) ⊤).hom ≫
      (I.cocomplex.X n).presheaf.map _ ≫
      (I.cocomplex.X n).presheaf.map (homOfLE e).op
    simp only [Hom.comp_app, Category.assoc]
    have hn := (Hom.mapPresheaf (R'.comparison.inv.f n)).naturality
      (eqToHom (by simp) : (⊤ : L.toScheme.Opens) ⟶
        j ⁻¹ᵁ (⊤ : U.toScheme.Opens)).op
    change (((restrictFunctor L.ι).obj (I.cocomplex.X n)).presheaf.map _ ≫
      Hom.app (R'.comparison.inv.f n) ⊤) =
      Hom.app (R'.comparison.inv.f n) (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) ≫
      (R'.resolution.cocomplex.X n).presheaf.map _ at hn
    rw [← Category.assoc (Hom.app (R'.comparison.inv.f n) _)
      ((R'.resolution.cocomplex.X n).presheaf.map _)]
    erw [← hn]
    simp only [Category.assoc]
    have hcan : Hom.app (R'.comparison.inv.f n) ⊤ ≫
        Hom.app (R'.comparison.hom.f n) ⊤ = 𝟙 _ := by
      rw [← Hom.comp_app, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
        HomologicalComplex.id_f, Hom.id_app]
    rw [← Category.assoc (Hom.app (R'.comparison.inv.f n) ⊤)
      (Hom.app (R'.comparison.hom.f n) ⊤), hcan, Category.id_comp]
    have hu := congrArg (fun f ↦ Hom.app f ⊤)
      ((restrictAdjunction j).unit.naturality (R.comparison.hom.f n))
    change Hom.app (R.comparison.hom.f n) ⊤ ≫
      Hom.app ((restrictAdjunction j).unit.app
        ((restrictFunctor U.ι).obj (I.cocomplex.X n))) ⊤ =
      Hom.app ((restrictAdjunction j).unit.app (R.resolution.cocomplex.X n)) ⊤ ≫
      Hom.app (Q.map (R.comparison.hom.f n)) (j ⁻¹ᵁ (⊤ : U.toScheme.Opens)) at hu
    rw [← Category.assoc (Hom.app ((restrictAdjunction j).unit.app
      (R.resolution.cocomplex.X n)) ⊤)
      (Hom.app (Q.map (R.comparison.hom.f n)) _), ← hu]
    simp only [Category.assoc]
    simp only [c, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Hom.comp_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
      restrictAdjunction_unit_app_app, restrictAppIso, Iso.refl_hom]
    erw [Category.id_comp, Category.id_comp]
    simp only [restrict_map, ← Functor.map_comp]
    congr 1
  let iR := (forget₂ _ AddCommGrpCat.{u}).mapIso
    (R.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p) ≪≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
  let iR' := (forget₂ _ AddCommGrpCat.{u}).mapIso
    (R'.resolution.isoRightDerivedObj
      (RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace) p) ≪≫
      (((RingedSpace.globalSectionsComplex R'.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).symm
  have hmap := moduleCohomologyFMap_of_augmentedLift j φ R'.resolution R.resolution
    β hβ a ha p
  change iR.hom ≫ H.map ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map β) ≫
    H.map a.inv ≫ iR'.inv = moduleCohomologyFMap j φ p at hmap
  change moduleCohomologyFMap j φ p ≫ iR'.hom ≫ H.map R'.sections.hom =
    iR.hom ≫ H.map R.sections.hom ≫ H.map r
  rw [← hmap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp, ← H.map_comp, hc, H.map_comp]


end AlgebraicGeometry.Scheme.Modules

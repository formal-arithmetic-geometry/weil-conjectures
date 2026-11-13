/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso
import WeilConjectures.AlgebraicGeometry.AffinePullbackSectionsUnitUncancelled

/-! # Pullback unit on affine sections models

## References

* Stacks Project, Tags 06Z0, 08DV, 08DW and 0AA7
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
private theorem cancel_model_comparisons
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Z : C} {A B : D} (s : A ≅ B) (f : A ⟶ F.obj W)
    (m : B ⟶ F.obj X) (e : X ≅ Z) (d : W ⟶ Z)
    (h : s.inv ≫ f ≫ F.map d = m ≫ F.map e.hom) :
    f ≫ F.map (d ≫ e.inv) = s.hom ≫ m := by
  have h' := congrArg (fun k ↦ s.hom ≫ k ≫ F.map e.inv) h
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_map, Category.comp_id] using h'

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The affine pullback unit on a K-flat associated-sheaf model is the localized
ordinary unit after the sections comparisons (Stacks, Tags 06Z0, 08DV, 08DW and 0AA7). -/
theorem exists_affinePullbackSections_model_unit
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage g).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (𝟙 (Spec B)) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (affineGlobalSections (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
          Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    [hT : (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)).Additive]
    [hP : (@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (Scheme.Modules.tensorPullback g)).Additive]
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M) :
    let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    let K := T.obj M
    let X := ((affineGlobalSections (𝟙 (Spec R))).mapHomologicalComplex (.up ℤ)).obj K
    let Z := (affineDerivedGlobalSections (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)
    let P : SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) :=
      Scheme.Modules.tensorPullback g
    letI : P.Additive := hP
    let U := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
    let adjP : P ⊣ RingedSpace.moduleDirectImage g.toLRSHom.toShHom :=
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
    let Y := ((affineGlobalSections (𝟙 (Spec B))).mapHomologicalComplex (.up ℤ)).obj
      ((P.mapHomologicalComplex (.up ℤ)).obj K)
    ∀ (s : Z ≅ DerivedCategory.Q.obj X),
      s.inv =
        (DerivedCategory.quotientCompQhIso _).inv.app X ≫
          (affineGlobalSections (𝟙 (Spec R))).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
          (affineGlobalSections (𝟙 (Spec R))).rightDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso _).hom.app K) ≫
          (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
            (DerivedCategory.Q.obj K) →
      ∃ (b : (affineDerivedGlobalSections (𝟙 (Spec B))).obj
          ((derivedPullback g).obj (DerivedCategory.Q.obj K)) ≅ DerivedCategory.Q.obj Y),
        (affineDerivedGlobalSections (𝟙 (Spec R))).map
            ((canonicalPullbackAdjunction g).unit.app (DerivedCategory.Q.obj K)) ≫
          r.hom.app ((derivedPullback g).obj (DerivedCategory.Q.obj K)) ≫
          U.mapDerivedCategory.map b.hom =
        s.hom ≫ DerivedCategory.Q.map
          (((affineGlobalSections (𝟙 (Spec R))).mapHomologicalComplex (.up ℤ)).map
              ((adjP.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
            (v.hom.mapHomologicalComplex (.up ℤ)).app
              ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫
          U.mapDerivedCategoryFactors.inv.app Y  := by
  dsimp only
  intro s hs
  let K := (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M
  let P : SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) :=
    Scheme.Modules.tensorPullback g
  have : P.Additive := hP
  let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
  let S := affineDerivedGlobalSections (𝟙 (Spec B))
  let U := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
  obtain ⟨hd, hc⟩ := affinePullbackModelComparisons_isIso g (hT := hT) M hM
  have : IsIso (affineModelPullbackComparison g K) := hd
  have : IsIso (affineModelSectionsComparison B PK) := hc
  let b := S.mapIso (asIso (affineModelPullbackComparison g K)) ≪≫
    (asIso (affineModelSectionsComparison B PK)).symm
  refine ⟨b, ?_⟩
  have h := affinePullbackSections_unit_uncancelled g v r hr K
  have hs' : s.inv = affineModelSectionsComparison R K := hs
  rw [← hs'] at h
  let aP := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  have h' := cancel_model_comparisons U.mapDerivedCategory s
    ((affineDerivedGlobalSections (𝟙 (Spec R))).map
      ((canonicalPullbackAdjunction g).unit.app (DerivedCategory.Q.obj K)) ≫
      r.hom.app ((derivedPullback g).obj (DerivedCategory.Q.obj K)))
    (DerivedCategory.Q.map
      (((affineGlobalSections (𝟙 (Spec R))).mapHomologicalComplex (.up ℤ)).map
          ((aP.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (v.hom.mapHomologicalComplex (.up ℤ)).app PK) ≫
      U.mapDerivedCategoryFactors.inv.app
        (((affineGlobalSections (𝟙 (Spec B))).mapHomologicalComplex (.up ℤ)).obj PK))
    (asIso (affineModelSectionsComparison B PK))
    (S.map (affineModelPullbackComparison g K))
    (by simpa only [Category.assoc, asIso_hom] using h)
  simpa only [K, PK, P, U, b, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.symm_hom, asIso_inv, Category.assoc] using h'

end AlgebraicGeometry

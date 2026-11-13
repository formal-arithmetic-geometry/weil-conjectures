/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Compatible pasted tensor-pullback adjunction

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem tensorPullback_preserves_kFlat
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
      P.obj M = SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
    (hm : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
      P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
        eqToHom (h N).symm)
    [P.Additive] :
    ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
      K.IsKFlatTensor → CochainComplex.IsKFlatTensor (R := X.sheaf)
        ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
  intro K hK
  let e : (P.mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.tensorPullbackComplex g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩ K :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (h (K.X i))) (by
      intro i j hij
      change eqToHom (h (K.X i)) ≫ _ = P.map (K.d i j) ≫ eqToHom (h (K.X j))
      rw [hm]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rfl)
  have ht := CochainComplex.isKFlat_pullback g.hom.base X.sheaf Y.sheaf
    ⟨g.hom.c⟩ K hK
  let := SheafOfModules.monoidalCategory X.sheaf
  intro F hF i
  exact (ht F hF i).of_iso
    (HomologicalComplex₂.total.mapIso
      ((((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj F).mapIso e.symm) (.up ℤ))

private theorem compatible_single_adjunction
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (f : X ⟶ Y)
    (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
    [P.Additive] (adj : P ⊣ moduleDirectImage f)
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ)))
    (habs : ∀ H : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings Y)),
      (L ⋙ H).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α H)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ))) :
    ∃ adj' : L ⊣ derivedModuleDirectImage f,
      ∀ K, adj'.unit.app (DerivedCategory.Qh.obj K) ≫
        (derivedModuleDirectImage f).map (α.app K) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (moduleDirectImage f).rightDerivedFunctorUnit.app
            ((P.mapHomotopyCategory (.up ℤ)).obj K) := by
  have := hL
  have := habs (derivedModuleDirectImage f)
  have : (derivedModuleDirectImage f ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit L ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X)) (.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism
      (SheafOfModules.{u} (moduleRings X)))
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
        (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives _)
          |>.isIso_of_isRightDerivedFunctor _ I) L
  let a := adj.mapHomotopyCategory (.up ℤ)
  refine ⟨a.derived
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X)) (.up ℤ))
    α (moduleDirectImage f).rightDerivedFunctorUnit, ?_⟩
  intro K
  exact a.derivedη_fac_app
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y)) (.up ℤ))
    α (moduleDirectImage f).rightDerivedFunctorUnit K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Elaborating the pasted comparison and unit uses several large sheaf-category instances.
/-- Successive tensor pullbacks and their derived functors have compatible
adjunctions; the left comparison is invertible on K-flat complexes. -/
theorem exists_pasted_tensorPullback_adjunction
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    let F := (moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)
    let R := derivedModuleDirectImage f ⋙ derivedModuleDirectImage g
    let β : F ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R :=
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
          (moduleDirectImage g).rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit
          (derivedModuleDirectImage g) ≫ (Functor.associator _ _ _).hom
    ∃ (G : HomotopyCategory (SheafOfModules.{u} (moduleRings Z)) (ComplexShape.up ℤ) ⥤
        HomotopyCategory (SheafOfModules.{u} (moduleRings X)) (ComplexShape.up ℤ))
      (adj : G ⊣ F)
      (L : DerivedCategory (SheafOfModules.{u} (moduleRings Z)) ⥤
        DerivedCategory (SheafOfModules.{u} (moduleRings X)))
      (adj' : L ⊣ R)
      (α : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh),
      (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ,
        K.IsKFlatTensor → IsIso
          (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
      ∀ K, adj'.unit.app (DerivedCategory.Qh.obj K) ≫ R.map (α.app K) =
        DerivedCategory.Qh.map (adj.unit.app K) ≫ β.app (G.obj K) := by
  obtain ⟨Pf, hf, hfm, haf, ⟨af⟩⟩ := exists_tensorModulePullback f
  obtain ⟨Pg, hg, hgm, hag, ⟨ag⟩⟩ := exists_tensorModulePullback g
  have := haf
  have := hag
  obtain ⟨Lf, αf, hLf, hKf, habsf⟩ :=
    exists_absolute_leftDerived_tensorModulePullback f Pf hf hfm
  obtain ⟨Lg, αg, hLg, hKg, habsg⟩ :=
    exists_absolute_leftDerived_tensorModulePullback g Pg hg hgm
  obtain ⟨df, hdf⟩ := compatible_single_adjunction f Pf af Lf αf hLf habsf
  obtain ⟨dg, hdg⟩ := compatible_single_adjunction g Pg ag Lg αg hLg habsg
  let G := Pg.mapHomotopyCategory (.up ℤ) ⋙ Pf.mapHomotopyCategory (.up ℤ)
  let L := Lg ⋙ Lf
  let α : DerivedCategory.Qh ⋙ L ⟶ G ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight αg Lf ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Pg.mapHomotopyCategory (.up ℤ)) αf ≫
      (Functor.associator _ _ _).inv
  refine ⟨G, (ag.mapHomotopyCategory (.up ℤ)).comp
    (af.mapHomotopyCategory (.up ℤ)), L, dg.comp df, α, ?_, ?_⟩
  · intro K hK
    have := hKg K hK
    have hfiso : IsIso (αf.app ((Pg.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :=
      hKf ((Pg.mapHomologicalComplex (.up ℤ)).obj K)
        (tensorPullback_preserves_kFlat g Pg hg hgm K hK)
    have hi : IsIso
        (Lf.map (αg.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
          αf.app ((Pg.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := inferInstance
    simp only [α, G, L, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Category.id_comp, Category.comp_id]
    exact hi
  · intro K
    simp only [Adjunction.comp_unit_app, α, G, L, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp,
      Category.comp_id, Functor.comp_map, Functor.map_comp, Category.assoc]
    have hn := df.unit.naturality
      (X := Lg.obj (DerivedCategory.Qh.obj K))
      (Y := DerivedCategory.Qh.obj ((Pg.mapHomotopyCategory (.up ℤ)).obj K)) (αg.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn
    have hb := (moduleDirectImage g).rightDerivedFunctorUnit.naturality
      (X := (Pg.mapHomotopyCategory (.up ℤ)).obj K)
      (Y := ((moduleDirectImage f).mapHomotopyCategory (.up ℤ)).obj
        ((Pf.mapHomotopyCategory (.up ℤ)).obj ((Pg.mapHomotopyCategory (.up ℤ)).obj K)))
      ((af.mapHomotopyCategory (.up ℤ)).unit.app
        ((Pg.mapHomotopyCategory (.up ℤ)).obj K))
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hb
    rw [← (derivedModuleDirectImage g).map_comp_assoc, ← hn, Functor.map_comp]
    rw [Category.assoc, ← Functor.map_comp, hdf, Functor.map_comp]
    rw [← Category.assoc, hdg, Category.assoc]
    rw [← reassoc_of% hb]
    simp only [Functor.comp_obj]

end

end AlgebraicGeometry.RingedSpace

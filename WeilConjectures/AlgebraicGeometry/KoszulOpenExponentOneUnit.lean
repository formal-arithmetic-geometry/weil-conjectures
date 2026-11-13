/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSectionsUnit
import WeilConjectures.AlgebraicGeometry.KoszulOpenAugmentationCechUnit
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomChainClassNaturality

/-! # The augmented exponent-one class is restriction of one

## References

* Stacks Project, Tags 08D1 and 08DC.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private theorem cechAugmentation_sections_unit
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (C : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    DerivedCategory.Q.map ((principalCechAugmentation r f).app C) ≫
      principalCechDerivedComparison r f C =
        affineOpenSectionsToDerived A (koszulOpen A r f) C := by
  let Sh := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let S := affineOpenSections A (koszulOpen A r f)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} Sh
  let J := I.obj C
  let i := (CochainComplex.toKInjectiveResolution.{u} Sh).app C
  have : QuasiIso i :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} Sh C).2
  have := principalCechAugmentation_quasiIso r f J
  let b := affineOpenSectionsDerivedUnit A (koszulOpen A r f)
  have hb : b.app J = (S.rightDerivedFunctorObjQIso J).inv := by
    simp [b, affineOpenSectionsDerivedUnit, Functor.rightDerivedFunctorObjQIso]
    rfl
  have hβ := (principalCechDerivedComparison_exists r f C).choose_spec J i
  change principalCechDerivedComparison r f C ≫
    S.rightDerivedFunctor.map (DerivedCategory.Q.map i) ≫
      (S.rightDerivedFunctorObjQIso J).hom ≫
        DerivedCategory.Q.map ((principalCechAugmentation r f).app J) =
      DerivedCategory.Q.map ((principalCechFunctor r f).map i) at hβ
  apply (cancel_mono (S.rightDerivedFunctor.map (DerivedCategory.Q.map i) ≫
    (S.rightDerivedFunctorObjQIso J).hom ≫
      DerivedCategory.Q.map ((principalCechAugmentation r f).app J))).mp
  simp only [Category.assoc]
  change DerivedCategory.Q.map ((principalCechAugmentation r f).app C) ≫
      principalCechDerivedComparison r f C ≫ _ = b.app C ≫ _
  rw [hβ]
  have hnat := b.naturality i
  change DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map i) ≫ b.app J =
    b.app C ≫ S.rightDerivedFunctor.map (DerivedCategory.Q.map i) at hnat
  calc
    _ = DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map i) ≫
        DerivedCategory.Q.map ((principalCechAugmentation r f).app J) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map ((principalCechAugmentation r f).naturality i).symm
    _ = _ := by
      rw [← Category.assoc, ← hnat, hb]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed exponent-one chain class evaluates to the ordinary sections unit. -/
theorem koszulOpen_exponent_one_unit
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    let c := fun e : ℕ ↦ H.map (koszulCechDerivedComparison A r f (koszulOpenSheafComplex A r f e))
        (H.map (DerivedCategory.Q.map (colimit.ι
          (koszulCechHomDiagram A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj
              (koszulOpenSheafComplex A r f e))) e))
          (koszulOpenHomStageClass A r f (koszulOpenSheafComplex A r f e) e (𝟙 _)))
    H.map (G.map (koszulOpenUnit A r f 0)) (c 0) =
      derivedOpenStructureUnit A (koszulOpen A r f)  := by
  let C := openStructureSheafComplex A
  let t : koszulOpenSheafComplex A r f 0 ⟶ C :=
    ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
        ComplexShape.embeddingDownNat)
  have hn := koszulOpenHom_chain_class_naturality A r f
    (koszulOpenSheafComplex A r f 0) C 0 (𝟙 _) t
  dsimp only at hn ⊢
  have ht : DerivedCategory.Q.map t = koszulOpenUnit A r f 0 := rfl
  rw [ht] at hn
  refine hn.trans ?_
  simp only [Category.id_comp]
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj C
  let K := CochainComplex.moduleHomComplex
    ((koszulOpenTail A r f 0).extend ComplexShape.embeddingDownNat) M
  let P := (principalCechFunctor r f).obj C
  let S := ((affineOpenSections A (koszulOpen A r f)).mapHomologicalComplex (.up ℤ)).obj C
  let j := koszulCechHomObjIso A r f M 0
  let i := colimit.ι (koszulCechHomDiagram A r f M) 0
  let k := j.inv ≫ i ≫ koszulCechComparison A r f C
  let x := koszulHomChainClass (koszulOpenHomTranspose A r f C 0 t)
  let η := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0
  have hk := η.inv.naturality k
  change HomologicalComplex.homologyMap k 0 ≫ (η.app P).inv =
    (η.app K).inv ≫ H.map (DerivedCategory.Q.map k) at hk
  dsimp only [koszulOpenHomStageClass, koszulCechDerivedComparison]
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  change H.map (principalCechDerivedComparison r f C)
    (((η.app K).inv ≫ H.map (DerivedCategory.Q.map j.inv) ≫
      H.map (DerivedCategory.Q.map i) ≫
        H.map (DerivedCategory.Q.map (koszulCechComparison A r f C))) x) = _
  have hmaps : H.map (DerivedCategory.Q.map j.inv) ≫
      H.map (DerivedCategory.Q.map i) ≫
        H.map (DerivedCategory.Q.map (koszulCechComparison A r f C)) =
      H.map (DerivedCategory.Q.map k) := by
    simp only [k, Functor.map_comp]
  rw [hmaps, ← hk]
  change H.map (principalCechDerivedComparison r f C)
    ((η.app P).inv (HomologicalComplex.homologyMap k 0 x)) = _
  have hu := koszulOpen_augmentation_cech_unit A r f
  change HomologicalComplex.homologyMap k 0 x =
    HomologicalComplex.homologyMap ((principalCechAugmentation r f).app C) 0
      (openStructureUnitClass A (koszulOpen A r f)) at hu
  rw [hu]
  let a := (principalCechAugmentation r f).app C
  have ha := η.inv.naturality a
  change HomologicalComplex.homologyMap a 0 ≫ (η.app P).inv =
    (η.app S).inv ≫ H.map (DerivedCategory.Q.map a) at ha
  change ((HomologicalComplex.homologyMap a 0 ≫ (η.app P).inv) ≫
    H.map (principalCechDerivedComparison r f C))
      (openStructureUnitClass A (koszulOpen A r f)) = _
  rw [ha, Category.assoc, ← Functor.map_comp, cechAugmentation_sections_unit.{u, w, v} A r f C]
  rfl

end AlgebraicGeometry

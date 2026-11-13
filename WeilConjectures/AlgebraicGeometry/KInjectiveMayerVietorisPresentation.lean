/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisExact
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisComparisons

/-! # The short exact complex presenting direct-image Mayer--Vietoris

## References

* Stacks Project, Cohomology, Tag 08BV.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The transported restriction functors require extra elaboration heartbeats.
/-- The injective representative gives a short exact sequence with comparisons of
its first two arrows to the derived units and the difference of restriction maps. -/
theorem schemeKInjective_mayerVietoris_presentation
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, Injective (I.X n))
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    ∃ (B C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (f : I ⟶ B) (g : B ⟶ C) (hz : f ≫ g = 0)
      (eB : DerivedCategory.Q.obj B ≅
        (schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⊞
        (schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj E))
      (eC : DerivedCategory.Q.obj C ≅
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E)),
      (ShortComplex.mk f g hz).ShortExact ∧
      DerivedCategory.Q.map f ≫ eB.hom =
        e.hom ≫ biprod.lift (adjU.unit.app E) (adjV.unit.app E) ∧
      DerivedCategory.Q.map g ≫ eC.hom = eB.hom ≫
        biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV E)) := by
  obtain ⟨eU, eV, eW, hu, hv, hru, hrv⟩ :=
    schemeOpenModuleImageComplex_comparisons X U V I E e adjU adjV adjUV
  let Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      schemeDerivedCategory X := DerivedCategory.Q
  have : PreservesBinaryBiproducts Q :=
    preservesBinaryBiproducts_of_preservesBiproducts Q
  let eB : DerivedCategory.Q.obj (schemeMayerVietorisB X U V I) ≅
      (schemeDerivedDirectImage U.ι).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⊞
      (schemeDerivedDirectImage V.ι).obj
        ((schemeOpenRestriction X V).mapDerivedCategory.obj E) :=
    Q.mapBiprod (schemeOpenModuleImageComplex X U I)
      (schemeOpenModuleImageComplex X V I) ≪≫ biprod.mapIso eU eV
  refine ⟨schemeMayerVietorisB X U V I, schemeOpenModuleImageComplex X (U ⊓ V) I,
    schemeMayerVietorisF X U V I, schemeMayerVietorisG X U V I,
    schemeMayerVietoris_zero X U V I, eB, eW,
    schemeMayerVietorisComplex_shortExact X U V hcover I hI, ?_, ?_⟩
  · dsimp only [schemeMayerVietorisF, eB, Iso.trans_hom, biprod.mapIso]
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      rw [← Category.assoc, biprod.lift_fst]
      simpa [Category.assoc] using hu
    · simp only [Category.assoc, biprod.map_snd]
      rw [← Category.assoc, biprod.lift_snd]
      simpa [Category.assoc] using hv
  · dsimp only [schemeMayerVietorisG, eB, Iso.trans_hom, biprod.mapIso]
    rw [← biprod.mapBiprod_hom_desc Q]
    simp only [Category.assoc]
    apply congrArg (fun k => (Q.mapBiprod
      (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I)).hom ≫ k)
    apply biprod.hom_ext'
    · simpa [Category.assoc] using hru
    · simpa [Category.assoc] using congrArg Neg.neg hrv

end AlgebraicGeometry

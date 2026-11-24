/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonRestriction

/-! # Derived comparisons for the fixed open direct-image complexes

## References

* Stacks Project, Cohomology, Tag 08BV (K-injective computation of open direct image) and
  Tag 08BS (preservation of K-injectivity by restriction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

private theorem mate_naturality
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {H : A ⥤ D} {K : D ⥤ A}
    (a : F ⊣ G) (b : H ⊣ K) (T : B ⥤ D) (α : F ⋙ T ≅ H)
    {M N : A} (f : M ⟶ N) :
    G.map (F.map f) ≫ (b.homEquiv _ _)
        (α.inv.app _ ≫ T.map (a.counit.app (F.obj N)) ≫ α.hom.app N) =
      (b.homEquiv _ _)
        (α.inv.app _ ≫ T.map (a.counit.app (F.obj M)) ≫ α.hom.app M) ≫
          K.map (H.map f) := by
  let ρ : F ⋙ G ⟶ H ⋙ K :=
    Functor.whiskerLeft (F ⋙ G) b.unit ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (F ⋙ G) α.inv ≫
          Functor.whiskerRight (Functor.whiskerLeft F a.counit) T ≫ α.hom) K
  simpa only [ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj, Adjunction.homEquiv_unit]
    using ρ.naturality f

set_option backward.isDefEq.respectTransparency true in
-- Elaborating the three computed comparisons checks the transported scheme functors.
/-- The three canonical direct-image complexes compute the derived direct images,
compatibly with the U and V units and both nested restriction maps. -/
theorem schemeOpenModuleImageComplex_comparisons
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    ∃ (eU : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X U I) ≅
        (schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj E))
      (eV : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X V I) ≅
        (schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj E))
      (eW : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X (U ⊓ V) I) ≅
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E)),
      DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I) ≫ eU.hom =
        e.hom ≫ adjU.unit.app E ∧
      DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X V I) ≫ eV.hom =
        e.hom ≫ adjV.unit.app E ∧
      DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U)) I) ≫ eW.hom =
          eU.hom ≫ schemeDerivedOpenDirectImageRestriction X
            (homOfLE inf_le_left) adjU adjUV E ∧
      DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) I) ≫ eW.hom =
          eV.hom ≫ schemeDerivedOpenDirectImageRestriction X
            (homOfLE inf_le_right) adjV adjUV E := by
  let cU := schemeOpenModuleImageComplexComparison X U I adjU
  let cV := schemeOpenModuleImageComplexComparison X V I adjV
  let cW := schemeOpenModuleImageComplexComparison X (U ⊓ V) I adjUV
  let tU := ((schemeOpenRestriction X U).mapDerivedCategory ⋙
    schemeDerivedDirectImage U.ι).mapIso e
  let tV := ((schemeOpenRestriction X V).mapDerivedCategory ⋙
    schemeDerivedDirectImage V.ι).mapIso e
  let tW := ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⋙
    schemeDerivedDirectImage (U ⊓ V).ι).mapIso e
  refine ⟨cU ≪≫ tU, cV ≪≫ tV, cW ≪≫ tW, ?_, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ tU.hom)
        (schemeOpenModuleImageComplexComparison_unit X U I adjU)).trans
          (adjU.unit.naturality e.hom).symm)
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ tV.hom)
        (schemeOpenModuleImageComplexComparison_unit X V I adjV)).trans
          (adjV.unit.naturality e.hom).symm)
  · have hn : schemeDerivedOpenDirectImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U)) adjU adjUV (DerivedCategory.Q.obj I) ≫
          tW.hom = tU.hom ≫ schemeDerivedOpenDirectImageRestriction X
            (homOfLE inf_le_left) adjU adjUV E :=
      (mate_naturality adjU adjUV
        (schemeOpenOverlapRestriction X (homOfLE inf_le_left)).mapDerivedCategory
        (schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left)) e.hom).symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ tW.hom)
        (schemeOpenModuleImageComplexComparison_restriction X
          (homOfLE (inf_le_left : U ⊓ V ≤ U)) I adjU adjUV)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => cU.hom ≫ f) hn).trans (Category.assoc _ _ _).symm)))
  · have hn : schemeDerivedOpenDirectImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) adjV adjUV (DerivedCategory.Q.obj I) ≫
          tW.hom = tV.hom ≫ schemeDerivedOpenDirectImageRestriction X
            (homOfLE inf_le_right) adjV adjUV E :=
      (mate_naturality adjV adjUV
        (schemeOpenOverlapRestriction X (homOfLE inf_le_right)).mapDerivedCategory
        (schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right)) e.hom).symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ tW.hom)
        (schemeOpenModuleImageComplexComparison_restriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V)) I adjV adjUV)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => cV.hom ≫ f) hn).trans (Category.assoc _ _ _).symm)))

end AlgebraicGeometry

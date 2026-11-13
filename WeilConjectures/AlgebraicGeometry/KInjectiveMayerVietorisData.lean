/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The concrete restriction/direct-image complex for Mayer--Vietoris

All objects and arrows below are constructed from the underived adjunction; no
existence theorem is used to choose the data.

## References

* Stacks Project, Cohomology, Tag 08BV.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

private theorem unit_comp_mate
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {H : A ⥤ D} {K : D ⥤ A}
    (a : F ⊣ G) (b : H ⊣ K) (T : B ⥤ D) (α : F ⋙ T ≅ H) (M : A) :
    a.unit.app M ≫ (b.homEquiv _ _)
      (α.inv.app _ ≫ T.map (a.counit.app (F.obj M)) ≫ α.hom.app M) =
        b.unit.app M := by
  rw [← b.homEquiv_naturality_left]
  have h : H.map (a.unit.app M) ≫
      (α.inv.app _ ≫ T.map (a.counit.app (F.obj M)) ≫ α.hom.app M) = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, α.inv.naturality]
    simp only [Functor.comp_map, Category.assoc]
    erw [← T.map_comp_assoc, a.left_triangle_components, T.map_id, Category.id_comp]
    exact α.inv_hom_id_app M
  rw [h]
  exact b.homEquiv_id M

/-- Restriction/direct-image adjunction transported along the open-site equivalence. -/
def schemeOpenModuleAdjunction (X : Scheme.{u}) (U : X.Opens) :
    schemeOpenRestriction X U ⊣ Scheme.Modules.pushforward U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
    (Scheme.Modules.overFunctorEquiv U).symm

/-- Restrict to an open and then apply underived direct image. -/
abbrev schemeOpenModuleImage (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
  schemeOpenRestriction X U ⋙ Scheme.Modules.pushforward U.ι

/-- Additivity of `schemeOpenModuleImage`. -/
instance schemeOpenModuleImage_additive (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenModuleImage X U).Additive :=
  Functor.Additive.mk (by intros; rfl)

/-- `schemeOpenModuleImage` preserves zero morphisms. -/
instance schemeOpenModuleImage_preservesZero (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenModuleImage X U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The restriction to a smaller open, expressed as the mate of the restricted counit. -/
def schemeOpenModuleImageRestriction (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    schemeOpenModuleImage X U ⟶ schemeOpenModuleImage X W :=
  Functor.whiskerLeft (schemeOpenModuleImage X U) (schemeOpenModuleAdjunction X W).unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (schemeOpenModuleImage X U) (schemeOpenRestrictionCompIso X i).inv ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (schemeOpenRestriction X U)
            (schemeOpenModuleAdjunction X U).counit) (schemeOpenOverlapRestriction X i) ≫
        (schemeOpenRestrictionCompIso X i).hom)
      (Scheme.Modules.pushforward W.ι)

/-- Restricting the unit further is the unit for the smaller open. -/
theorem schemeOpenModuleImage_unit_restriction (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (schemeOpenModuleAdjunction X U).unit.app M ≫
      (schemeOpenModuleImageRestriction X i).app M =
        (schemeOpenModuleAdjunction X W).unit.app M := by
  exact unit_comp_mate (schemeOpenModuleAdjunction X U) (schemeOpenModuleAdjunction X W)
    (schemeOpenOverlapRestriction X i) (schemeOpenRestrictionCompIso X i) M

/-- The complex whose degree n sections over T are Iⁿ(T ∩ U). -/
abbrev schemeOpenModuleImageComplex (X : Scheme.{u}) (U : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  ((schemeOpenModuleImage X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- The termwise restriction unit. -/
def schemeOpenModuleImageComplexUnit (X : Scheme.{u}) (U : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    I ⟶ schemeOpenModuleImageComplex X U I where
  f n := (schemeOpenModuleAdjunction X U).unit.app (I.X n)
  comm' i j _ := ((schemeOpenModuleAdjunction X U).unit.naturality (I.d i j)).symm

/-- Termwise restriction between the direct-image complexes. -/
def schemeOpenModuleImageComplexRestriction (X : Scheme.{u}) {W U : X.Opens}
    (i : W ⟶ U)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    schemeOpenModuleImageComplex X U I ⟶ schemeOpenModuleImageComplex X W I :=
  ((schemeOpenModuleImageRestriction X i).mapHomologicalComplex (ComplexShape.up ℤ)).app I

/-- The middle term of the concrete Mayer--Vietoris complex. -/
abbrev schemeMayerVietorisB (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  schemeOpenModuleImageComplex X U I ⊞ schemeOpenModuleImageComplex X V I

/-- The first arrow is the pair of restriction units. -/
def schemeMayerVietorisF (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    I ⟶ schemeMayerVietorisB X U V I :=
  biprod.lift (schemeOpenModuleImageComplexUnit X U I)
    (schemeOpenModuleImageComplexUnit X V I)

/-- The second arrow is the difference of restrictions to the intersection. -/
def schemeMayerVietorisG (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    schemeMayerVietorisB X U V I ⟶ schemeOpenModuleImageComplex X (U ⊓ V) I :=
  biprod.desc (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I)
    (-(schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I))

/-- The two arrows of the concrete diagram compose to zero. -/
theorem schemeMayerVietoris_zero (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    schemeMayerVietorisF X U V I ≫ schemeMayerVietorisG X U V I = 0 := by
  have h (W A : X.Opens) (i : W ⟶ A) :
      schemeOpenModuleImageComplexUnit X A I ≫
        schemeOpenModuleImageComplexRestriction X i I =
          schemeOpenModuleImageComplexUnit X W I := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact schemeOpenModuleImage_unit_restriction X i (I.X n)
  simp only [schemeMayerVietorisF, schemeMayerVietorisG, biprod.lift_desc,
    Preadditive.comp_neg, h, add_neg_cancel]

/-- The concrete short complex, without any exactness claim in its definition. -/
def schemeMayerVietorisComplex (X : Scheme.{u}) (U V : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    ShortComplex (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  ShortComplex.mk (schemeMayerVietorisF X U V I) (schemeMayerVietorisG X U V I)
    (schemeMayerVietoris_zero X U V I)

end AlgebraicGeometry

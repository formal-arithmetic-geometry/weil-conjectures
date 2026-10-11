/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Unit laws for the derived pullback

The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` (`AlgebraicGeometry.Etale.leftDerivedUpperStarId`) and
the composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) satisfy the two unit laws. Both are
checked on the image of the homotopy category, where they are the unit laws
`AlgebraicGeometry.Etale.upperStarComp_id_left` and `AlgebraicGeometry.Etale.upperStarComp_id_right`
of the underived pullbacks, read through the counits of the derived pullbacks.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_id_left_hom_app`
- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_id_right_hom_app`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

open DerivedCategory

variable {X : Scheme.{u}}

/-- On the image `Qh P` of a complex, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is the identity
isomorphism of the underived pullback, through the counit of the derived pullback. -/
lemma leftDerivedUpperStarId_hom_app_Qh_obj
    (P : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (leftDerivedUpperStarId A X).hom.app (Qh.obj P) =
      (𝟙 X)^*[A].leftDerivedFunctorCounit.app P ≫
        Qh.map ((NatTrans.mapHomotopyCategory (Etale.upperStarId A X).hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) := by
  have hfac := NatTrans.congr_app
    (𝟙 X)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac P
  have hnat := Functor.mapDerivedCategoryNatIso_fach (Etale.upperStarId A X) P
  have hid := NatTrans.congr_app (congrArg Iso.hom
    (Functor.mapDerivedCategoryIdIso_factorsh (Sheaf X.smallEtaleTopology A))) P
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hfac hid
  simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hfac, Category.assoc, Functor.map_comp]
  congr 1
  have hid' : (Functor.mapDerivedCategoryIdIso (Sheaf X.smallEtaleTopology A)).hom.app (Qh.obj P) =
      (𝟭 (Sheaf X.smallEtaleTopology A)).mapDerivedCategoryFactorsh.hom.app P ≫
        Qh.map ((Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) := by
    erw [Category.comp_id, Category.comp_id] at hid
    exact hid
  rw [hid', reassoc_of% hnat]

variable {Y : Scheme.{u}}

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The right unit law for the composition isomorphisms of the underived pullbacks, on the
homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_right (h : Y ⟶ X)
    (P : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (𝟙 X)^*[A] (h)^*[A] (h)^*[A]
        (upperStarComp A h (𝟙 X) h (Category.comp_id h).symm) P ≫
      ((h)^*[A].mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (Etale.upperStarId A X).hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj,
    Functor.mapHomotopyCategoryIdIso_hom_app]
  have hnt : (NatTrans.mapHomotopyCategory (Etale.upperStarId A X).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (Etale.upperStarId A X).hom (.up ℤ)).app K) := rfl
  rw [hnt, ← Functor.map_comp, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  have hK : (𝟙 X)^*[A].mapHomologicalComplexCompHom (h)^*[A] (h)^*[A]
        (upperStarComp A h (𝟙 X) h (Category.comp_id h).symm) K ≫
      ((h)^*[A].mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (Etale.upperStarId A X).hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app K) = 𝟙 _ := by
    ext n : 1
    simp only [Functor.mapHomologicalComplexCompHom, Etale.upperStarComp_id_right]
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Functor.mapHomologicalComplex_map_f, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      HomologicalComplex.id_f, Category.id_comp, Category.assoc]
    erw [Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
    exact (h)^*[A].map_id _
  rw [hK]
  exact (HomotopyCategory.quotient _ (.up ℤ)).map_id _

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The left unit law for the composition isomorphisms of the underived pullbacks, on the
homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_left (p : Y ⟶ X)
    (P : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (p)^*[A] (𝟙 Y)^*[A] (p)^*[A]
        (upperStarComp A (𝟙 Y) p p (Category.id_comp p).symm) P ≫
      (NatTrans.mapHomotopyCategory (Etale.upperStarId A Y).hom (.up ℤ)).app
          (((p)^*[A].mapHomotopyCategory (.up ℤ)).obj P) ≫
        (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app
          (((p)^*[A].mapHomotopyCategory (.up ℤ)).obj P) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  erw [Functor.mapHomotopyCategoryIdIso_hom_app]
  have hnt : (NatTrans.mapHomotopyCategory (Etale.upperStarId A Y).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (Etale.upperStarId A Y).hom (.up ℤ)).app
          (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K)) := rfl
  erw [hnt, ← Functor.map_comp]
  have hK : (p)^*[A].mapHomologicalComplexCompHom (𝟙 Y)^*[A] (p)^*[A]
        (upperStarComp A (𝟙 Y) p p (Category.id_comp p).symm) K ≫
      (NatTrans.mapHomologicalComplex (Etale.upperStarId A Y).hom (.up ℤ)).app
          (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app
          (((p)^*[A].mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := by
    ext n : 1
    simp only [Functor.mapHomologicalComplexCompHom, Etale.upperStarComp_id_left]
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
      HomologicalComplex.id_f, Category.id_comp, Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
    rfl
  refine (congrArg (HomotopyCategory.quotient _ (.up ℤ)).map hK).trans ?_
  exact (HomotopyCategory.quotient _ (.up ℤ)).map_id _

/-- **The right unit law** for the composition isomorphisms of the derived pullbacks:
`L(h ≫ 𝟙)^* ≅ L(𝟙)^* ⋙ Lh^*` followed by `L(𝟙)^* ≅ 𝟭` is the identity. -/
@[reassoc]
lemma leftDerivedUpperStarComp_id_right_hom_app (h : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A h (𝟙 X) h (Category.comp_id h).symm).hom.app K ≫
      L((h)^*[A]).map ((leftDerivedUpperStarId A X).hom.app K) = 𝟙 _ := by
  suffices H : (leftDerivedUpperStarComp A h (𝟙 X) h (Category.comp_id h).symm).hom ≫
      Functor.whiskerRight (leftDerivedUpperStarId A X).hom L((h)^*[A]) =
        (Functor.leftUnitor _).inv from NatTrans.congr_app H K
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app]
  rw [← cancel_mono ((h)^*[A].leftDerivedFunctorCounit.app P),
    leftDerivedUpperStarId_hom_app_Qh_obj, Functor.map_comp, Category.assoc, Category.assoc]
  erw [counit_naturality A h]
  rw [leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc,
    ← Functor.map_comp, mapHomotopyCategoryCompHom_upperStarComp_id_right]
  erw [Qh.map_id, Category.comp_id, Category.id_comp]

/-- **The left unit law** for the composition isomorphisms of the derived pullbacks:
`L(𝟙 ≫ p)^* ≅ Lp^* ⋙ L(𝟙)^*` followed by `L(𝟙)^* ≅ 𝟭` is the identity. -/
@[reassoc]
lemma leftDerivedUpperStarComp_id_left_hom_app (p : Y ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A (𝟙 Y) p p (Category.id_comp p).symm).hom.app K ≫
      (leftDerivedUpperStarId A Y).hom.app (L((p)^*[A]).obj K) = 𝟙 _ := by
  suffices H : (leftDerivedUpperStarComp A (𝟙 Y) p p (Category.id_comp p).symm).hom ≫
      Functor.whiskerLeft L((p)^*[A]) (leftDerivedUpperStarId A Y).hom =
        (Functor.rightUnitor _).inv from NatTrans.congr_app H K
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  have hn := (leftDerivedUpperStarId A Y).hom.naturality ((p)^*[A].leftDerivedFunctorCounit.app P)
  simp only [Functor.id_map, Functor.comp_obj] at hn
  rw [← cancel_mono ((p)^*[A].leftDerivedFunctorCounit.app P), Category.assoc, ← hn,
    leftDerivedUpperStarId_hom_app_Qh_obj,
    leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc]
  rw [← Functor.map_comp, mapHomotopyCategoryCompHom_upperStarComp_id_left, Qh.map_id,
    Category.comp_id,
    Category.id_comp]

end Etale

end AlgebraicGeometry

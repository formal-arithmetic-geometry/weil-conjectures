/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

/-!
# Coherence of the composition isomorphisms of derived pro-étale pullbacks

The composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp`) and the identity isomorphisms
`L(𝟙 X)^* ≅ 𝟭` (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarId`) of the derived pullbacks
on pro-étale sheaves satisfy the associativity and unit laws: on the image of a complex they
are the corresponding isomorphisms of the underived pullbacks, read through the counits of the
derived pullbacks, and those satisfy the laws (`AlgebraicGeometry.ProEtale.upperStarComp_assoc`,
`AlgebraicGeometry.ProEtale.upperStarComp_id_left`,
`AlgebraicGeometry.ProEtale.upperStarComp_id_right`).

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence`.

## Main results

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit`,
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarId_hom_app_Qh_obj`: the composition and
  identity isomorphisms on the image of a complex.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_assoc_app`: the associativity law.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_id_left_app`,
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_id_right_app`: the unit laws.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme DerivedCategory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Counit

variable {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)

/-- On the image `Qh X` of a complex, the composition isomorphism
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` is the composition isomorphism `(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*` of
the underived pullbacks, through the counits of the derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit
    (X : HomotopyCategory (Sheaf (ProEt.topology R) A) (.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app (Qh.obj X) ≫
        L((g₁)^*[A]).map ((g₂)^*[A].leftDerivedFunctorCounit.app X) ≫
        (g₁)^*[A].leftDerivedFunctorCounit.app (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj X) =
      (g₁ ≫ g₂)^*[A].leftDerivedFunctorCounit.app X ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (g₂)^*[A] (g₁)^*[A] (g₁ ≫ g₂)^*[A]
          (upperStarComp A g₁ g₂) X) := by
  have hfac (F : Sheaf (ProEt.topology R) A ⥤ Sheaf (ProEt.topology T) A) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (Y : HomotopyCategory (Sheaf (ProEt.topology R) A) (.up ℤ)) :
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        F.mapDerivedCategoryFactorsh.hom.app Y = F.leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hfac₂ (Y : HomotopyCategory (Sheaf (ProEt.topology R) A) (.up ℤ)) :
      (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        (g₂)^*[A].mapDerivedCategoryFactorsh.hom.app Y =
          (g₂)^*[A].leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app (g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hfac₁ (Y : HomotopyCategory (Sheaf (ProEt.topology S) A) (.up ℤ)) :
      (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj Y) ≫
        (g₁)^*[A].mapDerivedCategoryFactorsh.hom.app Y =
          (g₁)^*[A].leftDerivedFunctorCounit.app Y :=
    NatTrans.congr_app (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  have hnat := (g₁)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((g₂)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app (Qh.obj X) ≫
      (g₂)^*[A].mapDerivedCategoryFactorsh.hom.app X)
  have hcomp := Functor.mapDerivedCategoryCompIso_fach (g₂)^*[A] (g₁)^*[A] X
  have hnatiso := Functor.mapDerivedCategoryNatIso_fach (upperStarComp A g₁ g₂) X
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hfac₂, ← hfac₁, ← hfac, ← reassoc_of% hnat, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.mapHomotopyCategoryCompHom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnatiso, ← hcomp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- On the image `Qh X` of a complex, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is the identity
isomorphism `(𝟙 X)^* ≅ 𝟭` of the underived pullback, through the counit of the derived
pullback. -/
lemma leftDerivedUpperStarId_hom_app_Qh_obj
    (X : HomotopyCategory (Sheaf (ProEt.topology T) A) (.up ℤ)) :
    (leftDerivedUpperStarId A T).hom.app (Qh.obj X) =
      (𝟙 T)^*[A].leftDerivedFunctorCounit.app X ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarId A T).hom (.up ℤ)).app X ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app X) := by
  have hfac := NatTrans.congr_app (𝟙 T)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have hnatiso := Functor.mapDerivedCategoryNatIso_fach (upperStarId A T) X
  have hid := NatTrans.congr_app
    (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh (Sheaf (ProEt.topology T) A))) X
  dsimp at hfac hid
  simp only [Category.comp_id] at hid
  simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc, hid]
  rw [← hfac, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← reassoc_of% hnatiso]

/-- Transport along an equality of morphisms commutes with the counits of the derived
pullbacks. -/
lemma leftDerivedUpperStarCongr_hom_app_Qh_obj_comp_counit {f g : T ⟶ S} (h : f = g)
    (X : HomotopyCategory (Sheaf (ProEt.topology S) A) (.up ℤ)) :
    (leftDerivedUpperStarCongr A h).hom.app (Qh.obj X) ≫ (g)^*[A].leftDerivedFunctorCounit.app X =
      (f)^*[A].leftDerivedFunctorCounit.app X ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarCongr A h).hom (.up ℤ)).app X) := by
  subst h
  simp [upperStarCongr]

/-- The naturality of the counit of `Lg^*`, with the composite functors unfolded. -/
@[reassoc]
lemma counit_naturality (g : T ⟶ S)
    {P Q : HomotopyCategory (Sheaf (ProEt.topology S) A) (.up ℤ)} (f : P ⟶ Q) :
    L((g)^*[A]).map (Qh.map f) ≫ (g)^*[A].leftDerivedFunctorCounit.app Q =
      (g)^*[A].leftDerivedFunctorCounit.app P ≫
        Qh.map (((g)^*[A].mapHomotopyCategory (.up ℤ)).map f) :=
  (g)^*[A].leftDerivedFunctorCounit.naturality f

end Counit

section Laws

variable {W X Y Z : Scheme.{u}}

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
lemma mapHomotopyCategoryCompHom_upperStarComp_quotient_obj (a : X ⟶ Y) (b : Y ⟶ Z)
    (K : CochainComplex (Sheaf (ProEt.topology Z) A) ℤ) :
    Functor.mapHomotopyCategoryCompHom (b)^*[A] (a)^*[A] (a ≫ b)^*[A] (upperStarComp A a b)
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (Functor.mapHomologicalComplexCompHom (b)^*[A] (a)^*[A] (a ≫ b)^*[A]
          (upperStarComp A a b) K) := by
  rw [Functor.map_comp]
  congr 1

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The left unit law of the underived pullbacks, on the homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_left (g : X ⟶ Y)
    (P : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (g)^*[A] (𝟙 X)^*[A] (𝟙 X ≫ g)^*[A]
        (upperStarComp A (𝟙 X) g) P ≫
      (NatTrans.mapHomotopyCategory (upperStarId A X).hom (.up ℤ)).app _ ≫
      (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app _ =
    (NatTrans.mapHomotopyCategory (upperStarCongr A (Category.id_comp g)).hom (.up ℤ)).app P := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have key : Functor.mapHomologicalComplexCompHom (g)^*[A] (𝟙 X)^*[A] (𝟙 X ≫ g)^*[A]
        (upperStarComp A (𝟙 X) g) K ≫
      (NatTrans.mapHomologicalComplex (upperStarId A X).hom (.up ℤ)).app
        (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app
        (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K) =
    (NatTrans.mapHomologicalComplex (upperStarCongr A (Category.id_comp g)).hom (.up ℤ)).app K := by
    ext n : 1
    have h := congrArg (fun e ↦ e.hom.app (K.X n)) (upperStarComp_id_left A g)
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp] at h
    simp only [Functor.mapHomologicalComplexCompHom, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
      Iso.refl_inv, NatTrans.id_app, Functor.mapHomologicalComplexIdIso_hom_app_f]
    have h' : (upperStarComp A (𝟙 X) g).hom.app (K.X n) ≫
        (upperStarId A X).hom.app ((g)^*[A].obj (K.X n)) =
        (upperStarCongr A (Category.id_comp g)).hom.app (K.X n) := by
      rw [h]; simp
    refine Eq.trans ?_ h'
    congr 1
    · exact Category.comp_id _
    · exact Category.comp_id _
  have := congrArg (HomotopyCategory.quotient _ (.up ℤ)).map key
  simp only [Functor.map_comp] at this
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  erw [Functor.mapHomotopyCategoryIdIso_hom_app]
  exact this

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The right unit law of the underived pullbacks, on the homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_id_right (f : X ⟶ Y)
    (P : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (𝟙 Y)^*[A] (f)^*[A] (f ≫ 𝟙 Y)^*[A]
        (upperStarComp A f (𝟙 Y)) P ≫
      ((f)^*[A].mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (upperStarId A Y).hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app P) =
    (NatTrans.mapHomotopyCategory (upperStarCongr A (Category.comp_id f)).hom (.up ℤ)).app P := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have key : Functor.mapHomologicalComplexCompHom (𝟙 Y)^*[A] (f)^*[A] (f ≫ 𝟙 Y)^*[A]
        (upperStarComp A f (𝟙 Y)) K ≫
      ((f)^*[A].mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (upperStarId A Y).hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app K) =
    (NatTrans.mapHomologicalComplex (upperStarCongr A (Category.comp_id f)).hom (.up ℤ)).app K := by
    ext n : 1
    have h := congrArg (fun e ↦ e.hom.app (K.X n)) (upperStarComp_id_right A f)
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp] at h
    simp only [Functor.mapHomologicalComplexCompHom, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
      Iso.refl_inv, NatTrans.id_app, Functor.mapHomologicalComplexIdIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f]
    have h' : (upperStarComp A f (𝟙 Y)).hom.app (K.X n) ≫
        (f)^*[A].map ((upperStarId A Y).hom.app (K.X n)) =
        (upperStarCongr A (Category.comp_id f)).hom.app (K.X n) := by
      rw [h]; simp [← Functor.map_comp]
    refine Eq.trans ?_ h'
    congr 1
    · exact Category.comp_id _
    · exact congrArg _ (Category.comp_id _)
  have e : (NatTrans.mapHomotopyCategory (upperStarId A Y).hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) = (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (upperStarId A Y).hom (.up ℤ)).app K) := rfl
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  erw [Functor.mapHomotopyCategoryIdIso_hom_app]
  rw [e, ← Functor.map_comp, Functor.mapHomotopyCategory_map, ← Functor.map_comp, key]
  rfl

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The associativity law of the underived pullbacks, on the homotopy category. -/
lemma mapHomotopyCategoryCompHom_upperStarComp_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (P : HomotopyCategory (Sheaf (ProEt.topology Z) A) (.up ℤ)) :
    Functor.mapHomotopyCategoryCompHom (h)^*[A] (f ≫ g)^*[A] ((f ≫ g) ≫ h)^*[A]
        (upperStarComp A (f ≫ g) h) P ≫
      Functor.mapHomotopyCategoryCompHom (g)^*[A] (f)^*[A] (f ≫ g)^*[A]
        (upperStarComp A f g) (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P) =
    (NatTrans.mapHomotopyCategory (upperStarCongr A (Category.assoc f g h)).hom (.up ℤ)).app P ≫
      Functor.mapHomotopyCategoryCompHom (g ≫ h)^*[A] (f)^*[A] (f ≫ g ≫ h)^*[A]
        (upperStarComp A f (g ≫ h)) P ≫
      ((f)^*[A].mapHomotopyCategory (.up ℤ)).map
        (Functor.mapHomotopyCategoryCompHom (h)^*[A] (g)^*[A] (g ≫ h)^*[A]
          (upperStarComp A g h) P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj,
    mapHomotopyCategoryCompHom_upperStarComp_quotient_obj,
    mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  erw [mapHomotopyCategoryCompHom_upperStarComp_quotient_obj]
  change (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _ =
    (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _ ≫ _
  rw [Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  ext n : 1
  have key := upperStarComp_hom_app_comp_upperStarComp_hom_app A f g h (K.X n)
  simp only [Functor.mapHomologicalComplexCompHom, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Functor.mapHomologicalComplex_map_f]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, Category.comp_id]
  exact key

variable {A}

/-- **Left unit law** for the composition isomorphisms of derived pullbacks:
`L(𝟙 ≫ g)^* ≅ Lg^* ⋙ L(𝟙)^* ≅ Lg^*` is the transport along `𝟙 ≫ g = g`. -/
lemma leftDerivedUpperStarComp_id_left (g : X ⟶ Y) :
    (leftDerivedUpperStarComp A (𝟙 X) g).hom ≫
        Functor.whiskerLeft L((g)^*[A]) (leftDerivedUpperStarId A X).hom =
      (leftDerivedUpperStarCongr A (Category.id_comp g)).hom := by
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono ((g)^*[A].leftDerivedFunctorCounit.app P)]
  have h₁ : L((𝟙 X)^*[A]).map ((g)^*[A].leftDerivedFunctorCounit.app P) ≫
      (leftDerivedUpperStarId A X).hom.app
        (Qh.obj (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) =
      (leftDerivedUpperStarId A X).hom.app (L((g)^*[A]).obj (Qh.obj P)) ≫
        (g)^*[A].leftDerivedFunctorCounit.app P :=
    (leftDerivedUpperStarId A X).hom.naturality ((g)^*[A].leftDerivedFunctorCounit.app P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← h₁, leftDerivedUpperStarId_hom_app_Qh_obj,
    leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc,
    leftDerivedUpperStarCongr_hom_app_Qh_obj_comp_counit, ← Functor.map_comp,
    mapHomotopyCategoryCompHom_upperStarComp_id_left]

/-- The component form of `leftDerivedUpperStarComp_id_left`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_id_left_app (g : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedUpperStarComp A (𝟙 X) g).hom.app K ≫
        (leftDerivedUpperStarId A X).hom.app (L((g)^*[A]).obj K) =
      (leftDerivedUpperStarCongr A (Category.id_comp g)).hom.app K :=
  NatTrans.congr_app (leftDerivedUpperStarComp_id_left g) K

/-- **Right unit law** for the composition isomorphisms of derived pullbacks:
`L(f ≫ 𝟙)^* ≅ L(𝟙)^* ⋙ Lf^* ≅ Lf^*` is the transport along `f ≫ 𝟙 = f`. -/
lemma leftDerivedUpperStarComp_id_right (f : X ⟶ Y) :
    (leftDerivedUpperStarComp A f (𝟙 Y)).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarId A Y).hom L((f)^*[A]) =
      (leftDerivedUpperStarCongr A (Category.comp_id f)).hom := by
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono ((f)^*[A].leftDerivedFunctorCounit.app P)]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, leftDerivedUpperStarId_hom_app_Qh_obj, Functor.map_comp, Category.assoc]
  erw [counit_naturality A f]
  rw [leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit_assoc,
    leftDerivedUpperStarCongr_hom_app_Qh_obj_comp_counit, ← Functor.map_comp,
    mapHomotopyCategoryCompHom_upperStarComp_id_right]

/-- The component form of `leftDerivedUpperStarComp_id_right`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_id_right_app (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedUpperStarComp A f (𝟙 Y)).hom.app K ≫
        L((f)^*[A]).map ((leftDerivedUpperStarId A Y).hom.app K) =
      (leftDerivedUpperStarCongr A (Category.comp_id f)).hom.app K :=
  NatTrans.congr_app (leftDerivedUpperStarComp_id_right f) K

/-- **Associativity** of the composition isomorphisms of derived pullbacks, on the image of a
complex. -/
lemma leftDerivedUpperStarComp_assoc_app_Qh_obj (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (P : HomotopyCategory (Sheaf (ProEt.topology Z) A) (.up ℤ)) :
    (leftDerivedUpperStarComp A (f ≫ g) h).hom.app (Qh.obj P) ≫
        (leftDerivedUpperStarComp A f g).hom.app (L((h)^*[A]).obj (Qh.obj P)) =
      (leftDerivedUpperStarCongr A (Category.assoc f g h)).hom.app (Qh.obj P) ≫
        (leftDerivedUpperStarComp A f (g ≫ h)).hom.app (Qh.obj P) ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A g h).hom.app (Qh.obj P)) := by
  rw [← cancel_mono (L((f)^*[A]).map (L((g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P)) ≫
    L((f)^*[A]).map ((g)^*[A].leftDerivedFunctorCounit.app
      (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) ≫
    (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj
      (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)))]
  have u₁ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A g h P
  have u₂ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A f (g ≫ h) P
  have u₃ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A f g
    (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)
  have u₄ := leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A (f ≫ g) h P
  have u₅ := leftDerivedUpperStarCongr_hom_app_Qh_obj_comp_counit A (Category.assoc f g h) P
  have n₁ := counit_naturality A f (Functor.mapHomotopyCategoryCompHom (h)^*[A] (g)^*[A]
    (g ≫ h)^*[A] (upperStarComp A g h) P)
  have n₂ : (leftDerivedUpperStarComp A f g).hom.app (L((h)^*[A]).obj (Qh.obj P)) ≫
      L((f)^*[A]).map (L((g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P)) =
      L((f ≫ g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P) ≫
        (leftDerivedUpperStarComp A f g).hom.app _ :=
    ((leftDerivedUpperStarComp A f g).hom.naturality _).symm
  have hL : ((leftDerivedUpperStarComp A (f ≫ g) h).hom.app (Qh.obj P) ≫
      (leftDerivedUpperStarComp A f g).hom.app (L((h)^*[A]).obj (Qh.obj P))) ≫
      L((f)^*[A]).map (L((g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P)) ≫
      L((f)^*[A]).map ((g)^*[A].leftDerivedFunctorCounit.app
        (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) ≫
      (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj
        (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) =
      ((f ≫ g) ≫ h)^*[A].leftDerivedFunctorCounit.app P ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (h)^*[A] (f ≫ g)^*[A] ((f ≫ g) ≫ h)^*[A]
          (upperStarComp A (f ≫ g) h) P) ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (g)^*[A] (f)^*[A] (f ≫ g)^*[A]
          (upperStarComp A f g) (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) := by
    simp only [Category.assoc]
    rw [reassoc_of% n₂, u₃, reassoc_of% u₄]
  have hR : ((leftDerivedUpperStarCongr A (Category.assoc f g h)).hom.app (Qh.obj P) ≫
      (leftDerivedUpperStarComp A f (g ≫ h)).hom.app (Qh.obj P) ≫
      L((f)^*[A]).map ((leftDerivedUpperStarComp A g h).hom.app (Qh.obj P))) ≫
      L((f)^*[A]).map (L((g)^*[A]).map ((h)^*[A].leftDerivedFunctorCounit.app P)) ≫
      L((f)^*[A]).map ((g)^*[A].leftDerivedFunctorCounit.app
        (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) ≫
      (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj
        (((h)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) =
      ((f ≫ g) ≫ h)^*[A].leftDerivedFunctorCounit.app P ≫
        Qh.map ((NatTrans.mapHomotopyCategory (upperStarCongr A (Category.assoc f g h)).hom
          (.up ℤ)).app P) ≫
        Qh.map (Functor.mapHomotopyCategoryCompHom (g ≫ h)^*[A] (f)^*[A] (f ≫ g ≫ h)^*[A]
          (upperStarComp A f (g ≫ h)) P) ≫
        Qh.map (((f)^*[A].mapHomotopyCategory (.up ℤ)).map
          (Functor.mapHomotopyCategoryCompHom (h)^*[A] (g)^*[A] (g ≫ h)^*[A]
            (upperStarComp A g h) P)) := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [u₁, Functor.map_comp_assoc, n₁, reassoc_of% u₂, reassoc_of% u₅]
  rw [hL, hR, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mapHomotopyCategoryCompHom_upperStarComp_assoc]

/-- **Associativity** of the composition isomorphisms of derived pullbacks: the two ways of
identifying `L(f ≫ g ≫ h)^*` with `Lh^* ⋙ Lg^* ⋙ Lf^*` agree. -/
@[reassoc]
lemma leftDerivedUpperStarComp_assoc_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Z) A)) :
    (leftDerivedUpperStarComp A (f ≫ g) h).hom.app K ≫
        (leftDerivedUpperStarComp A f g).hom.app (L((h)^*[A]).obj K) =
      (leftDerivedUpperStarCongr A (Category.assoc f g h)).hom.app K ≫
        (leftDerivedUpperStarComp A f (g ≫ h)).hom.app K ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A g h).hom.app K) := by
  have := Localization.natTrans_ext (L := Qh) (W := HomotopyCategory.quasiIso _ (.up ℤ))
    (τ := (leftDerivedUpperStarComp A (f ≫ g) h).hom ≫
      Functor.whiskerLeft L((h)^*[A]) (leftDerivedUpperStarComp A f g).hom)
    (τ' := (leftDerivedUpperStarCongr A (Category.assoc f g h)).hom ≫
      (leftDerivedUpperStarComp A f (g ≫ h)).hom ≫
      Functor.whiskerRight (leftDerivedUpperStarComp A g h).hom L((f)^*[A]))
    fun P ↦ by
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      exact leftDerivedUpperStarComp_assoc_app_Qh_obj f g h P
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using NatTrans.congr_app this K

end Laws

end AlgebraicGeometry.ProEtale

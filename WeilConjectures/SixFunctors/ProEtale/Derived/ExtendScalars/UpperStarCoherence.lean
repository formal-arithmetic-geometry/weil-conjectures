/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStarCounit
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence

/-!
# Coherence of the commutation of derived scalar extension with `Lg^*`

The isomorphisms `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S` of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso` are compatible with the
identity isomorphisms `L(𝟙 Y)^* ≅ 𝟭`, with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` and with the transport along equalities of morphisms
(blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section HomotopyCategory

/-- On the image of a complex, `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is induced
by `sheafExtendScalarsCompUpperStarIso` degreewise. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (C : HomologicalComplex (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app
        ((HomotopyCategory.quotient _ _).obj C) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom (.up ℤ)).app C) := by
  simp only [mapHomotopyCategorySheafExtendScalarsCompUpperStarIso, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  erw [Category.id_comp, Category.comp_id]
  rfl

/-- `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is compatible with the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭`. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_id (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (𝟙 X)).hom.app K ≫
        ((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (ProEtale.upperStarId (ModuleCat.{u + 1} R) X).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (ProEtale.upperStarId (ModuleCat.{u + 1} S) X).hom
        (.up ℤ)).app
          (((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_obj_as, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact congrArg (fun f ↦ f.hom)
    (sheafExtendScalarsCompUpperStarIso_hom_app_id (algebraMap R S) X (C.X n))

/-- `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is compatible with the composition
isomorphisms `(g₁ ≫ g)^* ≅ g^* ⋙ g₁^*`. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_comp {T Z Y : Scheme.{u}}
    (g₁ : T ⟶ Z) (g : Z ⟶ Y)
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (g₁ ≫ g)).hom.app K ≫
        ((sheafExtendScalars (algebraMap R S) T).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom
          (.up ℤ)).app
            (((sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).obj K) ≫
        ((g₁)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K) ≫
        (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g₁).hom.app
          (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S (g₁ ≫ g) C,
    mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S g C]
  erw [mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S g₁
    (((g)^*[ModuleCat.{u + 1} R].mapHomologicalComplex (.up ℤ)).obj C)]
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_obj_as, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact congrArg (fun f ↦ f.hom)
    (sheafExtendScalarsCompUpperStarIso_hom_app_comp (algebraMap R S) g₁ g (C.X n))

end HomotopyCategory

variable [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the identifications
`L(𝟙 Y)^* ≅ 𝟭`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_id
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Y).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom.app K) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom.app
        (L(sheafExtendScalars (algebraMap R S) Y).obj K) := by
  have key : (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom ≫
      Functor.whiskerRight (leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom
        L(sheafExtendScalars (algebraMap R S) Y) ≫ (Functor.leftUnitor _).hom =
      Functor.whiskerLeft L(sheafExtendScalars (algebraMap R S) Y)
        (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom ≫ (Functor.rightUnitor _).hom := by
    apply Functor.leftDerived_ext (LF := L(sheafExtendScalars (algebraMap R S) Y))
      (α := (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit)
      (W := HomotopyCategory.quasiIso _ (.up ℤ))
    ext K
    have hα := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S (𝟙 Y) K
    have hE := (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit.naturality
      ((NatTrans.mapHomotopyCategory (ProEtale.upperStarId (ModuleCat.{u + 1} R) Y).hom
        (.up ℤ)).app K)
    have hS := (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom.naturality
      ((sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit.app K)
    dsimp at hE hS
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Category.assoc]
    rw [leftDerivedUpperStarId_hom_app_Qh, Functor.map_comp, Category.assoc]
    erw [Category.id_comp, hE, ← hS]
    rw [leftDerivedUpperStarId_hom_app_Qh]
    simp only [leftDerivedUpperStarSheafExtendScalarsCounit,
      leftDerivedSheafExtendScalarsUpperStarCounit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at hα
    rw [reassoc_of% hα, ← Functor.map_comp,
      mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_id]
  simpa using NatTrans.congr_app key K

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_comp {T : Scheme.{u}} (g₁ : T ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (g₁ ≫ g)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) T).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) g₁ g).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        L((g₁)^*[ModuleCat.{u + 1} S]).map
          ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g₁).hom.app
          (L((g)^*[ModuleCat.{u + 1} R]).obj K) := by
  have key : (leftDerivedUpperStarExtendScalarsIso R S (g₁ ≫ g)).hom =
      Functor.whiskerLeft _ (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarExtendScalarsIso R S g).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (leftDerivedUpperStarExtendScalarsIso R S g₁).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) g₁ g).inv _ := by
    apply Functor.leftDerived_ext
      (LF := L((g₁ ≫ g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) T))
      (α := leftDerivedUpperStarSheafExtendScalarsCounit R S (g₁ ≫ g))
      (W := HomotopyCategory.quasiIso _ (.up ℤ))
    ext K
    have h₀ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S (g₁ ≫ g) K
    have h₁ := leftDerivedUpperStarComp_inv_app_Qh (ModuleCat.{u + 1} R) g₁ g K
    have h₂ := (sheafExtendScalars (algebraMap R S) T).leftDerivedFunctorCounit.naturality
      ((NatTrans.mapHomotopyCategory
        (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).inv (.up ℤ)).app K)
    have h₃ := (leftDerivedUpperStarExtendScalarsIso R S g₁).hom.naturality
      (((g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit.app K)
    have h₄ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g₁
      (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K)
    have h₅ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g K
    have h₆ := ((g₁)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit.naturality
      ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K)
    have h₇ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom.naturality
      ((sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit.app K)
    have h₈ := leftDerivedUpperStarComp_hom_app_Qh (ModuleCat.{u + 1} S) g₁ g
      (((sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).obj K)
    have h₉ := mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_comp R S g₁ g K
    simp only [leftDerivedUpperStarSheafExtendScalarsCounit,
      leftDerivedSheafExtendScalarsUpperStarCounit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at h₀ h₄ h₅ ⊢
    dsimp at h₂ h₃ h₆ h₇
    sorry
  have := NatTrans.congr_app key K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at this
  rw [this]
  simp [← Functor.map_comp]

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the transport
`leftDerivedUpperStarCongr` along an equality of morphisms. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_congr {g' : Z ⟶ Y} (h : g = g')
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Z).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} R) h).hom.app K) =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} S) h).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g').hom.app K := by
  subst h
  simp

end AlgebraicGeometry.ProEtale

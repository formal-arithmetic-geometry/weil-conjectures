/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Projection
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit

/-!
# Derived pullback, extension and restriction of scalars

Let `S` be an algebra over a noetherian commutative ring `R` and `g : Z ⟶ Y` a morphism of
schemes. The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived scalar extension `Ψ = - ⊗ᴸ_R S` with the
derived pullback (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`) and the
commutation `Lg^* Res ≅ Res Lg^*` of restriction of scalars with the derived pullback
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`) are mates along the
adjunctions `Ψ ⊣ Res` (blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

omit [IsNoetherianRing R] in
/-- The mate of `g^*(S ⊗_R -) ≅ S ⊗_R g^*` along extension and restriction of scalars is the
commutation `g^* (Res M) ≅ Res (g^* M)` of
`AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso`. -/
lemma upperStarRestrictScalarsMap_eq :
    upperStarRestrictScalarsMap R S g = (upperStarRestrictScalarsIso (algebraMap R S) g).hom := by
  have hA : (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)
        (upperStarRestrictScalarsMap R S g)).natTrans =
      conjugateEquiv ((sheafExtendScalarsAdjunction (algebraMap R S) Y).comp
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g))
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).comp
          (sheafExtendScalarsAdjunction (algebraMap R S) Z))
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv :=
    iterated_mateEquiv_conjugateEquiv _ _ _ _ _
  rw [sheafExtendScalarsCompUpperStarIso, conjugateIsoEquiv_symm_apply_inv,
    Equiv.apply_symm_apply] at hA
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g)
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Y) (algebraMap R S))
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) (algebraMap R S))
    (TwoSquare.mk _ _ _ _ (lowerStarCompSheafComposeCoextendScalarsIso R S g).inv)
  rw [mateEquiv_symm_lowerStarCompSheafComposeCoextendScalarsIso] at h
  exact ((Equiv.eq_symm_apply _).2 hA).trans (h.trans rfl)


omit [IsNoetherianRing R] in
/-- On the image of an object of the homotopy category, the commutation
`Lg^* Res ≅ Res Lg^*` is induced, through the counits of the derived pullbacks, by
`g^* Res ≅ Res g^*`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app_Qh_obj
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} S)) (.up ℤ)) :
    (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) g).hom.app
        (DerivedCategory.Qh.obj K) ≫
      (Sheaf.derivedRestrictScalars _ (algebraMap R S)).map
        ((g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit.app K) ≫
      (Sheaf.restrictScalars (ProEt.topology Z) (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app
        (((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).obj K) =
    L((g)^*[ModuleCat.{u + 1} R]).map
        ((Sheaf.restrictScalars (ProEt.topology Y)
          (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app K) ≫
      (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit.app
        (((Sheaf.restrictScalars _ (algebraMap R S)).mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
          (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) := by
  have hsq := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj
    (upperStarRestrictScalarsIso (algebraMap R S) g) K
  have hS := (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh K
  have hR := (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    (((Sheaf.restrictScalars _ (algebraMap R S)).mapHomotopyCategory (.up ℤ)).obj K)
  have hn := (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app
      K)
  have hsq' : (Functor.mapDerivedCategorySquareIso
        (upperStarRestrictScalarsIso (algebraMap R S) g)).hom.app (DerivedCategory.Qh.obj K) ≫
      D(Sheaf.restrictScalars (ProEt.topology Z) (algebraMap R S)).map
        ((g)^*[ModuleCat S].mapDerivedCategoryFactorsh.hom.app K) ≫
      (Sheaf.restrictScalars (ProEt.topology Z) (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app
        (((g)^*[ModuleCat S].mapHomotopyCategory (.up ℤ)).obj K) =
      D((g)^*[ModuleCat R]).map
        ((Sheaf.restrictScalars (ProEt.topology Y)
          (algebraMap R S)).mapDerivedCategoryFactorsh.hom.app K) ≫
      (g)^*[ModuleCat R].mapDerivedCategoryFactorsh.hom.app
        (((Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S)).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
          (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) := by
    rw [← hsq]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [leftDerivedUpperStarRestrictScalarsIso_hom_app]
  have hS' : (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat S) g).inv.app
      (DerivedCategory.Qh.obj K) ≫ (g)^*[ModuleCat S].leftDerivedFunctorCounit.app K =
      (g)^*[ModuleCat S].mapDerivedCategoryFactorsh.hom.app K := by
    rw [← hS]
    exact Iso.inv_hom_id_app_assoc _ _ _
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [hS']
  erw [hsq']
  dsimp at hn
  erw [← reassoc_of% hn]
  erw [reassoc_of% hR]


/-- The isomorphism `Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))` has identity inverse
components. -/
private lemma mapHomotopyCategoryCompIso_refl_inv_app {V W V' : Type*} [Category V] [Category W]
    [Category V'] [Preadditive V] [Preadditive W] [Preadditive V'] (F : V ⥤ W) (G : W ⥤ V')
    [F.Additive] [G.Additive] (K : HomotopyCategory V (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 ((F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact (HomotopyCategory.quotient _ _).map_id _

omit [IsNoetherianRing R] in
/-- The counit form of `upperStarRestrictScalarsMap_eq` on homotopy categories. -/
lemma mapHomotopyCategory_upperStarRestrictScalarsIso_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} S)) (.up ℤ)) :
    ((sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
            (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) ≫
      ((sheafExtendScalarsAdjunction (algebraMap R S) Z).mapHomotopyCategory (.up ℤ)).counit.app
        (((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).obj K) =
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).inv.app
        (((Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S)).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      ((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
        (((sheafExtendScalarsAdjunction (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).counit.app
          K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hU (d : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} S)) :
      (sheafExtendScalars (algebraMap R S) Z).map
          ((upperStarRestrictScalarsIso (algebraMap R S) g).hom.app d) ≫
        (sheafExtendScalarsAdjunction (algebraMap R S) Z).counit.app
          ((g)^*[ModuleCat.{u + 1} S].obj d) =
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv.app
          ((Sheaf.restrictScalars (ProEt.topology Y) (algebraMap R S)).obj d) ≫
        (g)^*[ModuleCat.{u + 1} S].map
          ((sheafExtendScalarsAdjunction (algebraMap R S) Y).counit.app d) := by
    rw [← upperStarRestrictScalarsMap_eq]
    exact mateEquiv_counit (sheafExtendScalarsAdjunction (algebraMap R S) Y)
      (sheafExtendScalarsAdjunction (algebraMap R S) Z)
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv d
  simp only [mapHomotopyCategorySheafExtendScalarsCompUpperStarIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    mapHomotopyCategoryCompIso_refl_inv_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, HomotopyCategory.quotient_obj_as]
  erw [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  exact hU (C.X n)

/-- The inverse form of `leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit`. -/
lemma leftDerivedUpperStarExtendScalarsIso_inv_app_comp_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedUpperStarExtendScalarsIso R S g).inv.app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedSheafExtendScalarsUpperStarCounit R S g).app K =
      (leftDerivedUpperStarSheafExtendScalarsCounit R S g).app K ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).inv.app K) := by
  rw [← cancel_epi ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app
    (DerivedCategory.Qh.obj K)), Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  simp

/-- The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived scalar extension with the derived pullback is
the mate, along the adjunctions `Ψ ⊣ Res`, of the commutation `Lg^* Res ≅ Res Lg^*` of
restriction of scalars with the derived pullback (blueprint `thm-trf-finite-coefficient-map`). -/
theorem mateEquiv_leftDerivedUpperStarExtendScalarsIso_inv :
    mateEquiv (leftDerivedSheafExtendScalarsAdjunction R S Y)
        (leftDerivedSheafExtendScalarsAdjunction R S Z)
        (leftDerivedUpperStarExtendScalarsIso R S g).inv =
      (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) g).hom := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
  intro K
  apply ((leftDerivedSheafExtendScalarsAdjunction R S Z).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rw [← cancel_mono ((g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit.app K)]
  have hm := mateEquiv_counit (leftDerivedSheafExtendScalarsAdjunction R S Y)
    (leftDerivedSheafExtendScalarsAdjunction R S Z)
    (leftDerivedUpperStarExtendScalarsIso R S g).inv (DerivedCategory.Qh.obj K)
  rw [hm]
  simp only [Category.assoc]
  erw [← (leftDerivedSheafExtendScalarsAdjunction R S Z).counit_naturality
    ((g)^*[ModuleCat S].leftDerivedFunctorCounit.app K)]
  rw [leftDerivedSheafExtendScalarsAdjunction_counit_app_Qh_obj]
  erw [leftDerivedSheafExtendScalarsAdjunction_counit_app_Qh_obj R S Z
    (((g)^*[ModuleCat S].mapHomotopyCategory (.up ℤ)).obj K)]
  simp only [← Functor.map_comp_assoc]
  have hΓ : (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) g).hom.app
        (DerivedCategory.Qh.obj K) ≫
      D(sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
        ((g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit.app K) ≫
      (sheafCompose (ProEt.topology Z)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapDerivedCategoryFactorsh.hom.app
        (((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).obj K) =
    L((g)^*[ModuleCat.{u + 1} R]).map
        ((sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapDerivedCategoryFactorsh.hom.app
            K) ≫
      (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit.app
        (((sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapHomotopyCategory
            (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
          (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) :=
    leftDerivedUpperStarRestrictScalarsIso_hom_app_Qh_obj R S g K
  rw [hΓ]
  have hκ := (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso (algebraMap R S) g).hom
        (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K)
  have hβ := (leftDerivedUpperStarExtendScalarsIso R S g).inv.naturality
    ((sheafCompose (ProEt.topology Y)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapDerivedCategoryFactorsh.hom.app K)
  have hl := (g)^*[ModuleCat S].leftDerivedFunctorCounit.naturality
    (((sheafExtendScalarsAdjunction (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).counit.app K)
  have hB := leftDerivedUpperStarExtendScalarsIso_inv_app_comp_counit R S g
    (((sheafCompose (ProEt.topology Y)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapHomotopyCategory (.up ℤ)).obj K)
  have hH := mapHomotopyCategory_upperStarRestrictScalarsIso_counit R S g K
  simp only [leftDerivedSheafExtendScalarsUpperStarCounit,
    leftDerivedUpperStarSheafExtendScalarsCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at hB
  dsimp at hκ hβ hl
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hβ, cancel_epi]
  simp only [Functor.map_comp, Category.assoc] at hκ
  rw [hl, reassoc_of% hB, reassoc_of% hκ]
  have hH' := congrArg DerivedCategory.Qh.map hH
  simp only [Functor.map_comp, Category.assoc] at hH' ⊢
  rw [hH']

end AlgebraicGeometry.ProEtale

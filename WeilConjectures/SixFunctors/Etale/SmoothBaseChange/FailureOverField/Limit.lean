/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition

/-!
# Survival of a cokernel element under cofiltered limits

TODO
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma mapDerivedCategorySingleFunctor_hom_app_eq (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X,
    Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma mapDerivedCategoryNatIso_hom_app_singleFunctor {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app X =
      (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq, mapDerivedCategorySingleFunctor_hom_app_eq]
  erw [mapDerivedCategoryNatIso_fac_assoc e ((HomologicalComplex.single C (.up ℤ) 0).obj X)]
  rw [Category.assoc]
  congr 1
  rw [← DerivedCategory.Q.map_comp]
  change _ = _ ≫ DerivedCategory.Q.map _
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  ext i
  by_cases hi : i = 0
  · subst hi
    have h' : e.hom.app (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).X 0) =
        F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ e.hom.app X ≫
          G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv := by
      rw [e.hom.naturality_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, h', HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq]
    erw [G.map_id, Category.comp_id, Category.id_comp, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

lemma mapDerivedCategoryCompIso_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (mapDerivedCategoryCompIso F G).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq, mapDerivedCategorySingleFunctor_hom_app_eq,
    mapDerivedCategorySingleFunctor_hom_app_eq]
  rw [← mapDerivedCategoryCompIso_fac F G]
  erw [Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  have := G.mapDerivedCategoryFactors.hom.naturality
    ((F.mapCochainComplexSingleFunctor 0).hom.app X)
  erw [reassoc_of% this]
  refine congrArg (_ ≫ ·) ?_
  erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  refine congrArg _ ?_
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToHom_map, Functor.mapHomologicalComplexCompIso,
      HomologicalComplex.comp_f, NatIso.mapHomologicalComplex]
    erw [Category.id_comp]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]
    erw [eqToHom_map, eqToHom_trans]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

@[simp]
lemma ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (X : C) :
    DerivedCategory.Plus.ι.map ((F.mapDerivedCategoryPlusSingleFunctor n).hom.app X) =
      (F.mapDerivedCategorySingleFunctor n).hom.app X := by
  rw [mapDerivedCategoryPlusSingleFunctor, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, DerivedCategory.Plus.singleFunctorιIso]
  erw [isoWhiskerRight_hom, whiskerRight_app, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
    Category.id_comp, Iso.symm_hom, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  exact Category.id_comp _

lemma mapDerivedCategoryPlusNatIso_hom_app_singleFunctor {F G : C ⥤ D} [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (mapDerivedCategoryPlusNatIso e).hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app X =
      (F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
        (DerivedCategory.Plus.singleFunctor D 0).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact mapDerivedCategoryNatIso_hom_app_singleFunctor e X

lemma mapDerivedCategoryPlusCompIso_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        G.mapDerivedCategoryPlus.map ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategoryPlusSingleFunctor 0).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map f) =
        G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app, hmap]
  exact mapDerivedCategoryCompIso_hom_app_singleFunctor F G X


lemma mapDerivedCategoryPlusNatIso_trans_compIso_hom_app_singleFunctor {F₁₂ : C ⥤ E}
    (F₂ : C ⥤ D) (F₁ : D ⥤ E) [F₁₂.Additive] [F₂.Additive] [F₁.Additive]
    [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁] (e : F₁₂ ≅ F₂ ⋙ F₁) (X : C) :
    (mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso F₂ F₁).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
      F₁.mapDerivedCategoryPlus.map ((F₂.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
      (F₁.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F₂.obj X) =
    (F₁₂.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor E 0).map (e.hom.app X) := by
  rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    mapDerivedCategoryPlusCompIso_hom_app_singleFunctor]
  exact mapDerivedCategoryPlusNatIso_hom_app_singleFunctor e X

end CategoryTheory.Functor



open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Single

/-- The composition isomorphism of the derived pullbacks at a sheaf placed in degree `0` is the
underived composition isomorphism, through the identifications `h^*(G[0]) ≅ (h^* G)[0]`. -/
lemma Etale.upperStarCompDerivedPlus_hom_app_singleFunctor {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      D+((h₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((h₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      (((h₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((h₂)^*[ModuleCat.{u + 1} Λ]).obj G) =
    (((h₁₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app G) := by
  exact Functor.mapDerivedCategoryPlusNatIso_trans_compIso_hom_app_singleFunctor _ _ _ G

end Single

section StageTransition

omit [CommRing Λ] in
/-- The naturality of a natural transformation between composites of functors, stated for
abstract functors so that its instances at concrete functors are checked syntactically. -/
lemma natTrans_app_comp_map_map {ℬ 𝒞 𝒞' 𝒟 : Type*} [Category* ℬ]
    [Category* 𝒞] [Category* 𝒞'] [Category* 𝒟] {P₁ : ℬ ⥤ 𝒞} {P₂ : 𝒞 ⥤ 𝒟} {Q₁ : ℬ ⥤ 𝒞'}
    {Q₂ : 𝒞' ⥤ 𝒟} (β : P₁ ⋙ P₂ ⟶ Q₁ ⋙ Q₂) {X Y : ℬ} (f : X ⟶ Y) :
    P₂.map (P₁.map f) ≫ β.app Y = β.app X ≫ Q₂.map (Q₁.map f) :=
  β.naturality f

variable {S T : Scheme.{u}}

/-- The transition map `R(πᵢ ≫ g)_*(πᵢ^* K) ⟶ R(πⱼ ≫ g)_*(πⱼ^* K)` between the derived direct
images of the pullbacks of a complex `K` on `T` to two schemes `Tᵢ`, `Tⱼ` over `T`, along a
morphism `ρ : Tⱼ ⟶ Tᵢ` over `T`: the transition map
`AlgebraicGeometry.Etale.lowerStarPlusTransition` along `ρ`, followed by the composition
isomorphism `ρ^* πᵢ^* ≅ πⱼ^*`. -/
noncomputable def Etale.overLowerStarTransition (g : T ⟶ S) {Tᵢ Tⱼ : Scheme.{u}} (πᵢ : Tᵢ ⟶ T)
    (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (hπ : ρ ≫ πᵢ = πⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((πᵢ ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      R+((πⱼ ≫ g)_*[ModuleCat.{u + 1} Λ]).obj (D+((πⱼ)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  Etale.lowerStarPlusTransition Λ ρ (πᵢ ≫ g) (πⱼ ≫ g) (by rw [← Category.assoc, hπ]) _ ≫
    R+((πⱼ ≫ g)_*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ πⱼ hπ.symm).inv.app K)

/-- The transition maps `AlgebraicGeometry.Etale.overLowerStarTransition` compose. -/
lemma Etale.overLowerStarTransition_comp (g : T ⟶ S) {Tᵢ Tⱼ Tₖ : Scheme.{u}} (πᵢ : Tᵢ ⟶ T)
    (πⱼ : Tⱼ ⟶ T) (πₖ : Tₖ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (ρ' : Tₖ ⟶ Tⱼ) (ρ'' : Tₖ ⟶ Tᵢ)
    (hπ : ρ ≫ πᵢ = πⱼ) (hπ' : ρ' ≫ πⱼ = πₖ) (hπ'' : ρ'' ≫ πᵢ = πₖ) (hρ : ρ' ≫ ρ = ρ'')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.overLowerStarTransition Λ g πᵢ πⱼ ρ hπ K ≫
        Etale.overLowerStarTransition Λ g πⱼ πₖ ρ' hπ' K =
      Etale.overLowerStarTransition Λ g πᵢ πₖ ρ'' hπ'' K := by
  subst hρ hπ hπ'
  have hc := Etale.lowerStarPlusTransition_comp Λ ρ ρ' (ρ' ≫ ρ) rfl (πᵢ ≫ g) ((ρ ≫ πᵢ) ≫ g)
    ((ρ' ≫ ρ ≫ πᵢ) ≫ g) (by rw [Category.assoc]) (by simp only [Category.assoc])
    (by simp only [Category.assoc]) (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hn := Etale.lowerStarPlusTransition_naturality Λ ρ' ((ρ ≫ πᵢ) ≫ g)
    ((ρ' ≫ ρ ≫ πᵢ) ≫ g) (by simp only [Category.assoc])
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ (ρ ≫ πᵢ) rfl).inv.app K)
  have A := Etale.upperStarCompDerivedPlus_assoc Λ ρ' ρ πᵢ (ρ' ≫ ρ) (ρ ≫ πᵢ) (ρ' ≫ ρ ≫ πᵢ) rfl rfl
    (Category.assoc _ _ _).symm K
  have A' : D+((ρ')^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ (ρ ≫ πᵢ) rfl).inv.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ' (ρ ≫ πᵢ) (ρ' ≫ ρ ≫ πᵢ)
        rfl).inv.app K =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ' ρ (ρ' ≫ ρ) rfl).inv.app
          (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (ρ' ≫ ρ) πᵢ (ρ' ≫ ρ ≫ πᵢ)
          (Category.assoc _ _ _).symm).inv.app K := by
    rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (ρ' ≫ ρ) πᵢ
        (ρ' ≫ ρ ≫ πᵢ) (Category.assoc _ _ _).symm).hom.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ' ρ (ρ' ≫ ρ) rfl).hom.app
          (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)), ← A]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rw [reassoc_of% A]
    simp
  simp only [Etale.overLowerStarTransition, Category.assoc]
  rw [reassoc_of% hn, ← hc]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [A']

/-- The transition map between the targets of the derived base-change maps over two schemes
`Tᵢ`, `Tⱼ` over `T`, along a morphism `ρ : Tⱼ ⟶ Tᵢ` over `T` covered by `b : Yⱼ ⟶ Yᵢ`: the
transition map `AlgebraicGeometry.Etale.targetTransitionPlus` at `πᵢ^* K`, followed by the
composition isomorphism `ρ^* πᵢ^* ≅ πⱼ^*`. -/
noncomputable def Etale.overTargetTransition {X Yᵢ Yⱼ Tᵢ Tⱼ : Scheme.{u}} (eᵢ : Yᵢ ⟶ Tᵢ)
    (hᵢ : Yᵢ ⟶ X) (eⱼ : Yⱼ ⟶ Tⱼ) (hⱼ : Yⱼ ⟶ X) (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ)
    (b : Yⱼ ⟶ Yᵢ) (wa : b ≫ eᵢ = eⱼ ≫ ρ) (wh : b ≫ hᵢ = hⱼ) (hπ : ρ ≫ πᵢ = πⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((hᵢ)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((eᵢ)^*[ModuleCat.{u + 1} Λ]).obj (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)) ⟶
      R+((hⱼ)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((eⱼ)^*[ModuleCat.{u + 1} Λ]).obj (D+((πⱼ)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
  Etale.targetTransitionPlus Λ eᵢ hᵢ ρ b eⱼ hⱼ wa wh _ ≫
    R+((hⱼ)_*[ModuleCat.{u + 1} Λ]).map (D+((eⱼ)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ πⱼ hπ.symm).inv.app K))

/-- The transition map from `T` to `Tᵢ`, followed by the transition map from `Tᵢ` to `Tⱼ`, is
the transition map from `T` to `Tⱼ`. -/
lemma Etale.targetTransitionPlus_comp_overTargetTransition {X Y Yᵢ Yⱼ Tᵢ Tⱼ : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (eᵢ : Yᵢ ⟶ Tᵢ) (hᵢ : Yᵢ ⟶ X) (eⱼ : Yⱼ ⟶ Tⱼ) (hⱼ : Yⱼ ⟶ X)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (aᵢ : Yᵢ ⟶ Y) (aⱼ : Yⱼ ⟶ Y) (waᵢ : aᵢ ≫ e = eᵢ ≫ πᵢ)
    (whᵢ : aᵢ ≫ h = hᵢ) (waⱼ : aⱼ ≫ e = eⱼ ≫ πⱼ) (whⱼ : aⱼ ≫ h = hⱼ) (ρ : Tⱼ ⟶ Tᵢ)
    (b : Yⱼ ⟶ Yᵢ) (wa : b ≫ eᵢ = eⱼ ≫ ρ) (wh : b ≫ hᵢ = hⱼ) (hπ : ρ ≫ πᵢ = πⱼ)
    (hb : b ≫ aᵢ = aⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.targetTransitionPlus Λ e h πᵢ aᵢ eᵢ hᵢ waᵢ whᵢ K ≫
        Etale.overTargetTransition Λ eᵢ hᵢ eⱼ hⱼ πᵢ πⱼ ρ b wa wh hπ K =
      Etale.targetTransitionPlus Λ e h πⱼ aⱼ eⱼ hⱼ waⱼ whⱼ K :=
  Etale.targetTransitionPlus_comp Λ e h πᵢ aᵢ eᵢ hᵢ waᵢ whᵢ ρ b eⱼ hⱼ wa wh πⱼ aⱼ hb hπ waⱼ
    whⱼ K

/-- The derived base-change maps over `Tᵢ` and over `Tⱼ` commute with the transition maps
`AlgebraicGeometry.Etale.overLowerStarTransition` and
`AlgebraicGeometry.Etale.overTargetTransition`. -/
lemma Etale.baseChange_app_comp_overTargetTransition {X Yᵢ Yⱼ Tᵢ Tⱼ : Scheme.{u}} {p : X ⟶ S}
    (g : T ⟶ S) {eᵢ : Yᵢ ⟶ Tᵢ} {hᵢ : Yᵢ ⟶ X} {eⱼ : Yⱼ ⟶ Tⱼ} {hⱼ : Yⱼ ⟶ X} {πᵢ : Tᵢ ⟶ T}
    {πⱼ : Tⱼ ⟶ T} (sqᵢ : CommSq eᵢ hᵢ (πᵢ ≫ g) p) (sqⱼ : CommSq eⱼ hⱼ (πⱼ ≫ g) p)
    (ρ : Tⱼ ⟶ Tᵢ) (b : Yⱼ ⟶ Yᵢ) (wa : b ≫ eᵢ = eⱼ ≫ ρ) (wh : b ≫ hᵢ = hⱼ)
    (hπ : ρ ≫ πᵢ = πⱼ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) sqᵢ).app (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        Etale.overTargetTransition Λ eᵢ hᵢ eⱼ hⱼ πᵢ πⱼ ρ b wa wh hπ K =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.overLowerStarTransition Λ g πᵢ πⱼ ρ hπ K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sqⱼ).app
          (D+((πⱼ)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have c := Etale.baseChange_app_comp_targetTransitionPlus Λ sqᵢ ρ (πⱼ ≫ g)
    (by rw [← Category.assoc, hπ]) sqⱼ b wa wh (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K)
  have n := natTrans_app_comp_map_map (P₁ := R+((πⱼ ≫ g)_*[ModuleCat.{u + 1} Λ]))
    (P₂ := D+((p)^*[ModuleCat.{u + 1} Λ])) (Q₁ := D+((eⱼ)^*[ModuleCat.{u + 1} Λ]))
    (Q₂ := R+((hⱼ)_*[ModuleCat.{u + 1} Λ])) (Etale.baseChange (ModuleCat.{u + 1} Λ) sqⱼ)
    (X := D+((ρ)^*[ModuleCat.{u + 1} Λ]).obj (D+((πᵢ)^*[ModuleCat.{u + 1} Λ]).obj K))
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) ρ πᵢ πⱼ hπ.symm).inv.app K)
  rw [Etale.overTargetTransition, reassoc_of% c, Etale.overLowerStarTransition,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [n]

end StageTransition

section Conversion

/-- The form of `AlgebraicGeometry.Etale.upperStarCompDerivedPlus_hom_app_singleFunctor` for the
inverse of the composition isomorphism. -/
lemma Etale.upperStarCompDerivedPlus_inv_app_singleFunctor {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      (((h₁₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G =
    D+((h₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((h₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      (((h₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((h₂)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).inv.app G) := by
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)), Iso.hom_inv_id_app_assoc,
    reassoc_of% Etale.upperStarCompDerivedPlus_hom_app_singleFunctor, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

variable {S T : Scheme.{u}}

/-- The transition map `AlgebraicGeometry.Etale.overLowerStarTransition` at a sheaf placed in
degree `0` is, through the identifications `π^*(G[0]) ≅ (π^* G)[0]`, the transition map of
higher direct images underlying `AlgebraicGeometry.Etale.higherDirectImageOverMap`. -/
lemma Etale.overLowerStarTransition_singleFunctor (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {U V : Over T} (φ : U ⟶ V) :
    Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
      R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((U.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) =
    R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      Etale.lowerStarPlusTransition Λ φ.left (V.hom ≫ g) (U.hom ≫ g)
        (by rw [← Category.assoc, Over.w])
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
      R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
        ((((φ.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
              (Over.w φ).symm).inv.app G)) := by
  have hn := Etale.lowerStarPlusTransition_naturality Λ φ.left (V.hom ≫ g) (U.hom ≫ g)
    (by rw [← Category.assoc, Over.w])
    ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G)
  rw [reassoc_of% hn, Etale.overLowerStarTransition, Category.assoc, ← Functor.map_comp,
    Etale.upperStarCompDerivedPlus_inv_app_singleFunctor, Functor.map_comp]

/-- In degree `q`, the transition map `AlgebraicGeometry.Etale.overLowerStarTransition` at a sheaf
placed in degree `0` is `AlgebraicGeometry.Etale.higherDirectImageOverMap`, through the
identifications `π^*(G[0]) ≅ (π^* G)[0]`. -/
lemma Etale.homologyFunctor_map_overLowerStarTransition (g : T ⟶ S)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over T}
    (φ : U ⟶ V) :
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.overLowerStarTransition Λ g V.hom U.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((U.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G)) =
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((V.hom ≫ g)_*[ModuleCat.{u + 1} Λ]).map
          ((((V.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G)) ≫
      Etale.higherDirectImageOverMap Λ g G q φ := by
  rw [← Functor.map_comp, Etale.overLowerStarTransition_singleFunctor,
    Etale.higherDirectImageOverMap, Etale.higherDirectImageTransition]
  simp only [Functor.map_comp]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

/-- The identification `e'^*(π^*(F[0])) ≅ (a^*(e^* F))[0]` for a commutative square
`a ≫ e = e' ≫ π`. -/
noncomputable def Etale.stageSingleIso {Y Y' T' : Scheme.{u}} (e : Y ⟶ T) (a : Y' ⟶ Y)
    (e' : Y' ⟶ T') (π : T' ⟶ T) (wa : a ≫ e = e' ≫ π)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    D+((e')^*[ModuleCat.{u + 1} Λ]).obj
        (D+((π)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        (((a)^*[ModuleCat.{u + 1} Λ]).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
  ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).symm ≪≫
      Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
    D+((a)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F) ≪≫
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app
      (((e)^*[ModuleCat.{u + 1} Λ]).obj F)

/-- The coherence of the composition isomorphisms of derived pullbacks underlying
`AlgebraicGeometry.Etale.overTargetTransition_stageSingleIso`: the inverse form of
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus_coherence`. -/
lemma Etale.upperStarCompDerivedPlus_coherence_inv {T₂ T₁ Y Y₂ Y₁ : Scheme.{u}} (e : Y ⟶ T)
    (e₂ : Y₂ ⟶ T₂) (e₁ : Y₁ ⟶ T₁) (π₂ : T₂ ⟶ T) (π₁ : T₁ ⟶ T₂) (π : T₁ ⟶ T)
    (a₂ : Y₂ ⟶ Y) (a₁ : Y₁ ⟶ Y₂) (a : Y₁ ⟶ Y) (ha : a₁ ≫ a₂ = a) (hπ : π₁ ≫ π₂ = π)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂) (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wa : a ≫ e = e₁ ≫ π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e₂ (a₁ ≫ e₂) rfl).inv.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e₂) wa₁).hom.app
        (D+((π₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₁ π₂ π hπ.symm).inv.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π (a ≫ e) wa).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).hom.app K =
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).inv.app K ≫
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a ha.symm).inv.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have C := Etale.upperStarCompDerivedPlus_coherence Λ e e₂ e₁ π₂ π₁ π a₂ a₁ a ha hπ wa₂ wa₁ wa K
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ a₂ a
      ha.symm).hom.app (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e (a₂ ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e) wa₂).hom.app K))]
  simp only [Category.assoc] at C ⊢
  rw [reassoc_of% C]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- The transition map `AlgebraicGeometry.Etale.overTargetTransition` at a sheaf placed in
degree `0` is, through the identifications `AlgebraicGeometry.Etale.stageSingleIso`, the transition
map of higher direct images underlying `AlgebraicGeometry.Etale.higherDirectImageOverMap`. -/
lemma Etale.overTargetTransition_stageSingleIso {X Y Tᵢ Tⱼ : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) {U V : Over Y} (φ : U ⟶ V) (eᵢ : V.left ⟶ Tᵢ) (eⱼ : U.left ⟶ Tⱼ)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (waᵢ : V.hom ≫ e = eᵢ ≫ πᵢ)
    (waⱼ : U.hom ≫ e = eⱼ ≫ πⱼ) (wa : φ.left ≫ eᵢ = eⱼ ≫ ρ) (hπ : ρ ≫ πᵢ = πⱼ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.overTargetTransition Λ eᵢ (V.hom ≫ h) eⱼ (U.hom ≫ h) πᵢ πⱼ ρ φ.left wa
        (by rw [← Category.assoc, Over.w]) hπ ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        (Etale.stageSingleIso Λ e U.hom eⱼ πⱼ waⱼ F).hom =
    R+((V.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom ≫
      Etale.lowerStarPlusTransition Λ φ.left (V.hom ≫ h) (U.hom ≫ h)
        (by rw [← Category.assoc, Over.w])
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F))) ≫
      R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        ((((φ.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
              (Over.w φ).symm).inv.app (((e)^*[ModuleCat.{u + 1} Λ]).obj F))) := by
  have hn := Etale.lowerStarPlusTransition_naturality Λ φ.left (V.hom ≫ h) (U.hom ≫ h)
    (by rw [← Category.assoc, Over.w]) (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom
  rw [reassoc_of% hn, Etale.overTargetTransition, Etale.targetTransitionPlus]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  -- the identity of isomorphisms in the derived category of `U`
  have hs := Etale.upperStarCompDerivedPlus_inv_app_singleFunctor Λ φ.left V.hom U.hom
    (Over.w φ).symm (((e)^*[ModuleCat.{u + 1} Λ]).obj F)
  have hc := Etale.upperStarCompDerivedPlus_coherence_inv Λ e eᵢ eⱼ πᵢ ρ πⱼ V.hom φ.left U.hom
    (Over.w φ) hπ waᵢ wa waⱼ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hnat := natTrans_app_comp_map_map (P₁ := D+((V.hom)^*[ModuleCat.{u + 1} Λ]))
    (P₂ := D+((φ.left)^*[ModuleCat.{u + 1} Λ])) (Q₁ := 𝟭 _)
    (Q₂ := D+((U.hom)^*[ModuleCat.{u + 1} Λ]))
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
      (Over.w φ).symm).inv
    (X := D+((e)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (Y := (DerivedCategory.Plus.singleFunctor _ 0).obj (((e)^*[ModuleCat.{u + 1} Λ]).obj F))
    ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  simp only [Etale.stageSingleIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] at hc ⊢
  rw [← hs, reassoc_of% hnat, reassoc_of% hc]

/-- In degree `q`, the transition map `AlgebraicGeometry.Etale.overTargetTransition` at a sheaf
placed in degree `0` is `AlgebraicGeometry.Etale.higherDirectImageOverMap`, through the
identifications `AlgebraicGeometry.Etale.stageSingleIso`. -/
lemma Etale.homologyFunctor_map_overTargetTransition {X Y Tᵢ Tⱼ : Scheme.{u}} (e : Y ⟶ T)
    (h : Y ⟶ X) {U V : Over Y} (φ : U ⟶ V) (eᵢ : V.left ⟶ Tᵢ) (eⱼ : U.left ⟶ Tⱼ)
    (πᵢ : Tᵢ ⟶ T) (πⱼ : Tⱼ ⟶ T) (ρ : Tⱼ ⟶ Tᵢ) (waᵢ : V.hom ≫ e = eᵢ ≫ πᵢ)
    (waⱼ : U.hom ≫ e = eⱼ ≫ πⱼ) (wa : φ.left ≫ eᵢ = eⱼ ≫ ρ) (hπ : ρ ≫ πᵢ = πⱼ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (Etale.overTargetTransition Λ eᵢ (V.hom ≫ h) eⱼ (U.hom ≫ h) πᵢ πⱼ ρ φ.left wa
          (by rw [← Category.assoc, Over.w]) hπ ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e U.hom eⱼ πⱼ waⱼ F).hom) =
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((V.hom ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSingleIso Λ e V.hom eᵢ πᵢ waᵢ F).hom) ≫
      Etale.higherDirectImageOverMap Λ h (((e)^*[ModuleCat.{u + 1} Λ]).obj F) q φ := by
  rw [← Functor.map_comp, Etale.overTargetTransition_stageSingleIso,
    Etale.higherDirectImageOverMap, Etale.higherDirectImageTransition]
  simp only [Functor.map_comp]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

end Conversion

end AlgebraicGeometry

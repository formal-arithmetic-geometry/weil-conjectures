/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionMapDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Invertibility of the derived base change map

Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be adjunctions of additive functors between abelian
categories with exact left adjoints `F : D ⥤ C` and `F' : D' ⥤ C'`, and let `N_D : D ⥤ D'`,
`N_C : C ⥤ C'` be exact functors with an isomorphism `α : N_D ⋙ F' ≅ F ⋙ N_C`. The mate of
the induced isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` under the derived adjunctions
`D(F) ⊣ RG` and `D(F') ⊣ RG'` is the derived base change map `RG ⋙ D(N_D) ⟶ D(N_C) ⋙ RG'`.

We show that it is an isomorphism as soon as the underived base change map
`G ⋙ N_D ⟶ N_C ⋙ G'` (the mate of `α`) is an isomorphism and `N_C` preserves K-injective
complexes (`CategoryTheory.Adjunction.isIso_mateEquiv_mapDerivedCategorySquareIso`): on a
K-injective complex `I`, both `RG (Q I)` and `RG' (Q (N_C I))` are computed without resolving,
and the derived base change map is the image of the underived one
(`CategoryTheory.UnboundedExactTower.localized_mate_cochain_normalization`).

When `F'` is only given through its total left derived functor `LF'` (with the derived
adjunction `LF' ⊣ RG'`), the square is `CategoryTheory.Functor.leftDerivedFunctorSquareIso α :
D(N_D) ⋙ LF' ≅ D(F) ⋙ D(N_C)`, and its mate is again invertible
(`CategoryTheory.Adjunction.isIso_mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso`).
On complexes, this square is the counit of `LF'` followed by the image of `α`
(`CategoryTheory.Functor.leftDerivedFunctorSquareIso_hom_app_Q_obj`,
`CategoryTheory.Functor.whiskerLeft_Q_leftDerivedFunctorSquareIso_hom`).
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions C']
  {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] [N_D.Additive] [N_C.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits N_D] [PreservesFiniteColimits N_D]
  [PreservesFiniteLimits N_C] [PreservesFiniteColimits N_C]

/-- **Invertibility of the derived base change map.** If the underived base change map
`G ⋙ N_D ⟶ N_C ⋙ G'` (the mate of `α`) is an isomorphism and `N_C` preserves K-injective
complexes, then the derived base change map `RG ⋙ D(N_D) ⟶ D(N_C) ⋙ RG'`, the mate of the
isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` induced by `α` under the derived adjunctions
`D(F) ⊣ RG` and `D(F') ⊣ RG'`, is an isomorphism. -/
theorem isIso_mateEquiv_mapDerivedCategorySquareIso (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : N_D ⋙ F' ≅ F ⋙ N_C) [N_C.PreservesKInjectiveComplexes]
    [IsIso (mateEquiv adj adj' α.hom).natTrans] :
    IsIso (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso α).hom).natTrans := by
  let β := (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategorySquareIso α).hom).natTrans
  have hI (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
      IsIso (β.app (DerivedCategory.Q.obj I)) := by
    have : CochainComplex.IsKInjective ((N_C.mapHomologicalComplex (.up ℤ)).obj I) :=
      Functor.PreservesKInjectiveComplexes.isKInjective_map I
    have h := UnboundedExactTower.localized_mate_cochain_normalization adj adj' α I
    have hu : IsIso (UnboundedExactTower.cochainUnit G I) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have hu' : IsIso (UnboundedExactTower.cochainUnit G'
        ((N_C.mapHomologicalComplex (.up ℤ)).obj I)) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have hc : IsIso ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' α.hom).natTrans (.up ℤ)).app I) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
        (asIso (mateEquiv adj adj' α.hom).natTrans) (.up ℤ)).hom.app I))
    have ht : IsIso (N_D.mapDerivedCategoryFactors.inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        N_D.mapDerivedCategory.map (UnboundedExactTower.cochainUnit G I) ≫
        β.app (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (N_C.mapDerivedCategoryFactors.hom.app I)) := by
      dsimp only [UnboundedExactTower.localizedSquare] at h
      dsimp only [β]
      rw [h]
      infer_instance
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using ht
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ β fun K ↦ ?_
  obtain ⟨I, hIi, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have := hI I hIi
  have hs : IsIso ((G.rightDerivedFunctor ⋙ N_D.mapDerivedCategory).map e.hom ≫
      β.app (DerivedCategory.Q.obj I)) := inferInstance
  rw [β.naturality e.hom] at hs
  exact IsIso.of_isIso_comp_right (β.app K)
    ((N_C.mapDerivedCategory ⋙ G'.rightDerivedFunctor).map e.hom)

section LeftDerived

variable [MonoidalCategory D'] [MonoidalPreadditive D'] [HasCountableCoproducts D']
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D'] [HasExactColimitsOfShape ℤ D']
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').obj X)]
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D']

/-- The isomorphism `D(N_D) ⋙ LF' ≅ D(F) ⋙ D(N_C)` induced by `α : N_D ⋙ F' ≅ F ⋙ N_C`, where
`LF'` is the total left derived functor of the exact functor `F'`: the identification
`LF' ≅ D(F')` (`CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory`) followed by the
isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` induced by `α`. -/
noncomputable def _root_.CategoryTheory.Functor.leftDerivedFunctorSquareIso
    (α : N_D ⋙ F' ≅ F ⋙ N_C) :
    N_D.mapDerivedCategory ⋙ F'.leftDerivedFunctor ≅
      F.mapDerivedCategory ⋙ N_C.mapDerivedCategory :=
  Functor.isoWhiskerLeft _ F'.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso α

/-- The mate of `CategoryTheory.Functor.leftDerivedFunctorSquareIso α` under `D(F) ⊣ RG` and the
derived adjunction `LF' ⊣ RG'` is the mate of `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` under
`D(F) ⊣ RG` and `D(F') ⊣ RG'`. -/
lemma mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso (adj : F ⊣ G) (adj' : F' ⊣ G')
    (α : N_D ⋙ F' ≅ F ⋙ N_C) :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction adj'.derivedAdjunction
      (Functor.leftDerivedFunctorSquareIso α).hom).natTrans =
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategorySquareIso α).hom).natTrans := by
  rw [derivedAdjunction_eq_ofNatIsoLeft]
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit, Functor.leftDerivedFunctorSquareIso]

/-- **Invertibility of the derived base change map**, for the derived adjunction `LF' ⊣ RG'`:
if the underived base change map `G ⋙ N_D ⟶ N_C ⋙ G'` is an isomorphism and `N_C` preserves
K-injective complexes, then the mate `RG ⋙ D(N_D) ⟶ D(N_C) ⋙ RG'` of
`CategoryTheory.Functor.leftDerivedFunctorSquareIso α` is an isomorphism. -/
theorem isIso_mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso (adj : F ⊣ G)
    (adj' : F' ⊣ G') (α : N_D ⋙ F' ≅ F ⋙ N_C) [N_C.PreservesKInjectiveComplexes]
    [IsIso (mateEquiv adj adj' α.hom).natTrans] :
    IsIso (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction adj'.derivedAdjunction
      (Functor.leftDerivedFunctorSquareIso α).hom).natTrans := by
  rw [mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso]
  exact isIso_mateEquiv_mapDerivedCategorySquareIso adj adj' α

end LeftDerived

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  {F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
  [F.Additive] [F'.Additive] [N_D.Additive] [N_C.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits N_D] [PreservesFiniteColimits N_D]
  [PreservesFiniteLimits N_C] [PreservesFiniteColimits N_C]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits F']
  [PreservesFiniteColimits F'] [PreservesFiniteLimits N_D] [PreservesFiniteColimits N_D]
  [PreservesFiniteLimits N_C] [PreservesFiniteColimits N_C] in
/-- The termwise isomorphism `F'(N_D P) ≅ N_C(F P)` of complexes induced by
`α : N_D ⋙ F' ≅ F ⋙ N_C`, written with the composition isomorphisms
`Functor.mapHomologicalComplexCompIso`, is the image of `α` under
`NatTrans.mapHomologicalComplex`. -/
lemma mapHomologicalComplexCompIso_comp_inv_app (α : N_D ⋙ F' ≅ F ⋙ N_C)
    (P : CochainComplex D ℤ) :
    (mapHomologicalComplexCompIso α (.up ℤ)).hom.app P ≫
        (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).inv.app P =
      (NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app P := by
  ext n
  exact Category.comp_id _

/-- On the image `Q P` of a complex, the isomorphism `D(N_D) ⋙ D(F') ≅ D(F) ⋙ D(N_C)` induced
by `α : N_D ⋙ F' ≅ F ⋙ N_C` is, up to the factorizations `Functor.mapDerivedCategoryFactors`
through `Q`, the image under `Q` of the termwise isomorphism `α`. -/
@[reassoc]
lemma mapDerivedCategorySquareIso_hom_app_Q_obj (α : N_D ⋙ F' ≅ F ⋙ N_C)
    (P : CochainComplex D ℤ) :
    (mapDerivedCategorySquareIso α).hom.app (DerivedCategory.Q.obj P) ≫
        N_C.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        N_C.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      F'.mapDerivedCategory.map (N_D.mapDerivedCategoryFactors.hom.app P) ≫
        F'.mapDerivedCategoryFactors.hom.app ((N_D.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((mapHomologicalComplexCompIso α (.up ℤ)).hom.app P ≫
          (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).inv.app P) := by
  rw [mapHomologicalComplexCompIso_comp_inv_app]
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have hc := mapDerivedCategoryCompIso_fac F N_C P
  have hc' := mapDerivedCategoryCompIso_fac N_D F' P
  have hi : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).hom.app P = 𝟙 _ := rfl
  have hi' : (mapHomologicalComplexCompIso (Iso.refl (N_D ⋙ F')) (.up ℤ)).hom.app P = 𝟙 _ :=
    rfl
  erw [hi, CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [hi', CategoryTheory.Functor.map_id, Category.comp_id] at hc'
  erw [hc, mapDerivedCategoryNatIso_fac]
  erw [← hc']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

variable [MonoidalCategory D'] [MonoidalPreadditive D'] [HasCountableCoproducts D']
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D'] [HasExactColimitsOfShape ℤ D']
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').obj X)]
  [∀ (X : D'), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D').flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D']

/-- On the image `Q P` of a complex, the isomorphism `D(N_D) ⋙ LF' ≅ D(F) ⋙ D(N_C)` of
`CategoryTheory.Functor.leftDerivedFunctorSquareIso α` is, up to the factorizations through `Q`
and `Qh`, the counit of `LF'` at `N_D P` followed by the image under `Q` of the termwise
isomorphism `α`:
```
LF' (D(N_D) (Q P)) ──α──▶ D(N_C) (D(F) (Q P))
       │                         │
LF' (Qh (N_D P))           Q (N_C (F P))
       │ counit                  ▲
       ▼                         │ Q(α_P)
Qh (F' (N_D P)) ════════ Q (F' (N_D P))
``` -/
@[reassoc]
lemma leftDerivedFunctorSquareIso_hom_app_Q_obj (α : N_D ⋙ F' ≅ F ⋙ N_C)
    (P : CochainComplex D ℤ) :
    (leftDerivedFunctorSquareIso α).hom.app (DerivedCategory.Q.obj P) ≫
        N_C.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        N_C.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      F'.leftDerivedFunctor.map (N_D.mapDerivedCategoryFactors.hom.app P ≫
          (DerivedCategory.quotientCompQhIso D').inv.app
            ((N_D.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F'.leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient D' (.up ℤ)).obj ((N_D.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (DerivedCategory.quotientCompQhIso C').hom.app
          ((F'.mapHomologicalComplex (.up ℤ)).obj ((N_D.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((mapHomologicalComplexCompIso α (.up ℤ)).hom.app P ≫
          (mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).inv.app P) := by
  have h₁ := mapDerivedCategorySquareIso_hom_app_Q_obj α P
  have h₂ := F'.leftDerivedFunctorIsoMapDerivedCategory_hom_app_quotient_obj
    ((N_D.mapHomologicalComplex (.up ℤ)).obj P)
  have h₃ := F'.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (N_D.mapDerivedCategoryFactors.hom.app P ≫
      (DerivedCategory.quotientCompQhIso D').inv.app ((N_D.mapHomologicalComplex (.up ℤ)).obj P))
  simp only [leftDerivedFunctorSquareIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% h₂, reassoc_of% h₃]
  simpa [← Functor.map_comp_assoc] using h₁

/-- **The isomorphism `CategoryTheory.Functor.leftDerivedFunctorSquareIso α` on complexes**, as an
identity of natural transformations of functors `CochainComplex D ℤ ⥤ DerivedCategory C'`: after
precomposition with `Q`, it is the counit of `LF'` on `N_D P` followed by the image under `Q` of
the termwise isomorphism `α`, all functors being composed explicitly (with associators). This
is the form of `CategoryTheory.Functor.leftDerivedFunctorSquareIso_hom_app_Q_obj` in which no
identification of objects by definitional unfolding is needed, so it can be instantiated with
concrete functors at no cost. -/
lemma whiskerLeft_Q_leftDerivedFunctorSquareIso_hom (α : N_D ⋙ F' ≅ F ⋙ N_C) :
    whiskerLeft DerivedCategory.Q (leftDerivedFunctorSquareIso α).hom =
      (Functor.associator _ _ _).inv ≫
      whiskerRight N_D.mapDerivedCategoryFactors.hom F'.leftDerivedFunctor ≫
      whiskerRight (whiskerLeft (N_D.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso D').inv) F'.leftDerivedFunctor ≫
      whiskerRight (Functor.associator _ _ _).inv F'.leftDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft _ F'.leftDerivedFunctorCounit ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.associator _ _ _).hom DerivedCategory.Qh ≫
      whiskerRight (whiskerLeft (N_D.mapHomologicalComplex (.up ℤ))
        (F'.mapHomotopyCategoryFactors (.up ℤ)).hom) DerivedCategory.Qh ≫
      whiskerRight (Functor.associator _ _ _).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft _ (DerivedCategory.quotientCompQhIso C').hom ≫
      whiskerRight (mapHomologicalComplexCompIso α (.up ℤ)).hom DerivedCategory.Q ≫
      (F ⋙ N_C).mapDerivedCategoryFactors.inv ≫
      whiskerLeft DerivedCategory.Q (mapDerivedCategoryCompIso F N_C).inv := by
  ext P
  have h₁ := leftDerivedFunctorSquareIso_hom_app_Q_obj α P
  have h₂ := mapDerivedCategoryCompIso_fac F N_C P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, Functor.comp_obj, Category.id_comp, Functor.map_id]
  have h₃ : (F'.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      ((N_D.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := by
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  rw [
    ← cancel_mono (D(N_C).map (F.mapDerivedCategoryFactors.hom.app P) ≫
      N_C.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ N_C)) (.up ℤ)).hom.app P))]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, h₂, Iso.inv_hom_id_app]
  simp [h₃]

end CategoryTheory.Functor

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.OpenImmersion

/-!
# Coefficient comparisons and the comparison of compactifications
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section CoeffCompatibleCongr

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B'] {RA : A' ⥤ A}
  {RB : B' ⥤ B} {F G H : B ⥤ A} {F' G' H' : B' ⥤ A'}

/-- Composition of compatible natural transformations, through two coefficient comparisons of
the middle functors with the same components. -/
lemma CoeffCompatible.comp_of_eq {ιF : RB ⋙ F ≅ F' ⋙ RA} {ιG ιG' : RB ⋙ G ≅ G' ⋙ RA}
    {ιH : RB ⋙ H ≅ H' ⋙ RA} {α : F ⟶ G} {α' : F' ⟶ G'} {β : G ⟶ H} {β' : G' ⟶ H'}
    (h₁ : CoeffCompatible ιF ιG α α') (h₂ : CoeffCompatible ιG' ιH β β')
    (hG : ∀ K, ιG.hom.app K = ιG'.hom.app K) : CoeffCompatible ιF ιH (α ≫ β) (α' ≫ β') := by
  intro K
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, reassoc_of% (h₁ K), hG, h₂ K,
    Category.assoc]

/-- Compatibility only depends on the components of the coefficient comparisons. -/
lemma CoeffCompatible.of_hom_app_eq {ιF ιF' : RB ⋙ F ≅ F' ⋙ RA} {ιG ιG' : RB ⋙ G ≅ G' ⋙ RA}
    {α : F ⟶ G} {α' : F' ⟶ G'} (h : CoeffCompatible ιF ιG α α')
    (hF : ∀ K, ιF'.hom.app K = ιF.hom.app K) (hG : ∀ K, ιG.hom.app K = ιG'.hom.app K) :
    CoeffCompatible ιF' ιG' α α' := by
  intro K
  rw [hF, h K, hG]

end CoeffCompatibleCongr

section RightDerivedCoeff

/-- The isomorphism `Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))` is the identity. -/
lemma mapHomotopyCategoryCompIso_refl_inv_app {V W V' : Type*} [Category V] [Category W]
    [Category V'] [Preadditive V] [Preadditive W] [Preadditive V'] {ι : Type*} (c : ComplexShape ι)
    (F : V ⥤ W) (G : W ⥤ V') [F.Additive] [G.Additive] (Y : HomotopyCategory V c) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv.app Y = 𝟙 _ := by
  have := (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom_inv_id_app Y
  rwa [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at this

/-- The components of the inverse of a pasted square. -/
lemma pasteTwoSquaresIso_inv_app {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category C₀] [Category C₁]
    [Category C₂] [Category D₀] [Category D₁] [Category D₂] {r₀ : D₀ ⥤ C₀} {r₁ : D₁ ⥤ C₁}
    {r₂ : D₂ ⥤ C₂} {G₁ : C₀ ⥤ C₁} {G₂ : C₁ ⥤ C₂} {F₁ : D₀ ⥤ D₁} {F₂ : D₁ ⥤ D₂}
    (e₁ : r₀ ⋙ G₁ ≅ F₁ ⋙ r₁) (e₂ : r₁ ⋙ G₂ ≅ F₂ ⋙ r₂) (X : D₀) :
    (pasteTwoSquaresIso e₁ e₂).inv.app X = e₂.inv.app (F₁.obj X) ≫ G₂.map (e₁.inv.app X) := by
  simp [pasteTwoSquaresIso]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D] [HasDerivedCategory D']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  {rC : C' ⥤ C} {rD : D' ⥤ D} [rC.Additive] [PreservesFiniteLimits rC]
  [PreservesFiniteColimits rC] [rD.Additive] [PreservesFiniteLimits rD]
  [PreservesFiniteColimits rD] {F : C ⥤ D} {F' : C' ⥤ D'} [F.Additive] [F'.Additive]

/-- The coefficient comparison `D(rC) ⋙ RF ≅ RF' ⋙ D(rD)` of right derived functors induced
by an isomorphism `F' ⋙ rD ≅ rC ⋙ F`, for exact `rC` and `rD`, when the unit of `RF` is an
isomorphism at the image under `rC` of every K-injective complex. -/
noncomputable def rightDerivedCoeffIso (e : F' ⋙ rD ≅ rC ⋙ F)
    (hG : ∀ (K : CochainComplex C' ℤ) [K.IsKInjective], IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((rC.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) :
    rC.mapDerivedCategory ⋙ F.rightDerivedFunctor ≅
      F'.rightDerivedFunctor ⋙ rD.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso _ _ hG).symm ≪≫
    Functor.rightDerivedFunctorNatIso e.symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

/-- The coefficient comparison `rightDerivedCoeffIso` in terms of the units of the right derived
functors. -/
lemma rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_hom_app (e : F' ⋙ rD ≅ rC ⋙ F)
    (hG : ∀ (K : CochainComplex C' ℤ) [K.IsKInjective], IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((rC.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (X : HomotopyCategory C' (ComplexShape.up ℤ)) :
    F.rightDerivedFunctorUnit.app ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        F.rightDerivedFunctor.map (rC.mapDerivedCategoryFactorsh.inv.app X) ≫
        (rightDerivedCoeffIso e hG).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (rC ⋙ F)) (ComplexShape.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app X) ≫
        rD.mapDerivedCategoryFactorsh.inv.app ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        rD.mapDerivedCategory.map (F'.rightDerivedFunctorUnit.app X) := by
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_of_isIso
    rC F hG
  have h₁ := Functor.rightDerivedNatTrans_app (rC.mapDerivedCategory ⋙ F.rightDerivedFunctor)
    (rC ⋙ F).rightDerivedFunctor (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit rC F)
    (rC ⋙ F).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ))
    (𝟙 _) X
  have h₂ := Functor.rightDerivedNatTrans_app (rC ⋙ F).rightDerivedFunctor
    (F' ⋙ rD).rightDerivedFunctor (rC ⋙ F).rightDerivedFunctorUnit
    (F' ⋙ rD).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ))
      DerivedCategory.Qh) X
  have h₃ := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac F' rD X
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at h₃
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app, NatTrans.id_app,
    Category.id_comp, Category.assoc, Category.assoc] at h₁
  rw [← cancel_epi (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (rC ⋙ F)) (ComplexShape.up ℤ)).inv.app X))]
  simp only [rightDerivedCoeffIso, Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_inv, Iso.refl_inv]
  rw [reassoc_of% h₁]
  dsimp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans, Iso.symm_hom]
  rw [reassoc_of% h₂, h₃, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The inverse of the coefficient comparison `rightDerivedCoeffIso` in terms of the units of
the right derived functors. -/
lemma rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_inv_app (e : F' ⋙ rD ≅ rC ⋙ F)
    (hG : ∀ (K : CochainComplex C' ℤ) [K.IsKInjective], IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((rC.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (X : HomotopyCategory C' (ComplexShape.up ℤ)) :
    rD.mapDerivedCategoryFactorsh.inv.app ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        rD.mapDerivedCategory.map (F'.rightDerivedFunctorUnit.app X) ≫
        (rightDerivedCoeffIso e hG).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app X ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (rC ⋙ F)) (ComplexShape.up ℤ)).inv.app X) ≫
        F.rightDerivedFunctorUnit.app ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        F.rightDerivedFunctor.map (rC.mapDerivedCategoryFactorsh.inv.app X) := by
  rw [← cancel_mono ((rightDerivedCoeffIso e hG).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_hom_app, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  simp

end RightDerivedCoeff

section CompIso

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]

/-- The inverse of the composition isomorphism `RF ⋙ RG ≅ RH` in terms of the units of the
right derived functors. -/
lemma rightDerivedFunctorUnit_app_comp_rightDerivedFunctorCompIso'_inv_app (F : C ⥤ D)
    (G : D ⥤ E) {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H) (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    H.rightDerivedFunctorUnit.app X ≫
        (Functor.rightDerivedFunctorCompIso' F G e).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app X ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app X) ≫
        G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have h₁ := Functor.rightDerivedNatTrans_app H.rightDerivedFunctor (F ⋙ G).rightDerivedFunctor
    H.rightDerivedFunctorUnit (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ))
      DerivedCategory.Qh) X
  have h₂ := Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) (F ⋙ G).rightDerivedFunctorUnit
    (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (𝟙 _) X
  simp only [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
    Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans, Iso.trans_inv,
    Iso.symm_inv, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom, Iso.refl_hom,
    NatTrans.comp_app, reassoc_of% h₁]
  rw [h₂]
  simp [Functor.rightDerivedFunctorCompUnit]

end CompIso

section CoeffComp

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C C' D D' E E' : Type*} [Category C] [Category C'] [Category D] [Category D']
  [Category E] [Category E'] [Abelian C] [Abelian C'] [Abelian D] [Abelian D'] [Abelian E]
  [Abelian E'] [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
  [HasDerivedCategory D'] [HasDerivedCategory E] [HasDerivedCategory E']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions D']
  {rC : C' ⥤ C} {rD : D' ⥤ D} {rE : E' ⥤ E} [rC.Additive] [PreservesFiniteLimits rC]
  [PreservesFiniteColimits rC] [rD.Additive] [PreservesFiniteLimits rD]
  [PreservesFiniteColimits rD] [rE.Additive] [PreservesFiniteLimits rE]
  [PreservesFiniteColimits rE]
  {F₁ : C ⥤ D} {F₂ : D ⥤ E} {H : C ⥤ E} {F₁' : C' ⥤ D'} {F₂' : D' ⥤ E'} {H' : C' ⥤ E'}
  [F₁.Additive] [F₂.Additive] [H.Additive] [F₁'.Additive] [F₂'.Additive] [H'.Additive]
  [F₁.PreservesKInjectiveComplexes] [F₁'.PreservesKInjectiveComplexes]

/-- The composition isomorphisms `RF₁ ⋙ RF₂ ≅ RH` are compatible with the coefficient
comparisons `rightDerivedCoeffIso`, provided the underlying isomorphisms are. -/
lemma coeffCompatible_rightDerivedFunctorCompIso' (e : F₁ ⋙ F₂ ≅ H) (e' : F₁' ⋙ F₂' ≅ H')
    (e₁ : F₁' ⋙ rD ≅ rC ⋙ F₁) (e₂ : F₂' ⋙ rE ≅ rD ⋙ F₂) (eH : H' ⋙ rE ≅ rC ⋙ H)
    (h₁ : ∀ (K : CochainComplex C' ℤ) [K.IsKInjective], IsIso (F₁.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((rC.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (h₂ : ∀ (K : CochainComplex D' ℤ) [K.IsKInjective], IsIso (F₂.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((rD.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (hH : ∀ (K : CochainComplex C' ℤ) [K.IsKInjective], IsIso (H.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((rC.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (hcomp : ∀ X : C', rE.map (e'.inv.app X) ≫ e₂.hom.app (F₁'.obj X) ≫
      F₂.map (e₁.hom.app X) ≫ e.hom.app (rC.obj X) = eH.hom.app X) :
    CoeffCompatible (pasteTwoSquaresIso (rightDerivedCoeffIso e₁ h₁) (rightDerivedCoeffIso e₂ h₂))
      (rightDerivedCoeffIso eH hH) (Functor.rightDerivedFunctorCompIso' F₁ F₂ e).hom
      (Functor.rightDerivedFunctorCompIso' F₁' F₂' e').hom := by
  have key : Functor.whiskerRight (Functor.rightDerivedFunctorCompIso' F₁' F₂' e').inv
        rE.mapDerivedCategory ≫
      (pasteTwoSquaresIso (rightDerivedCoeffIso e₁ h₁) (rightDerivedCoeffIso e₂ h₂)).inv =
      (rightDerivedCoeffIso eH hH).inv ≫ Functor.whiskerLeft rC.mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso' F₁ F₂ e).inv := by
    refine Functor.rightDerived_ext (H'.rightDerivedFunctor ⋙ rE.mapDerivedCategory)
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit H' rE)
      (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ)) _ _ _ ?_
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app', Category.assoc]
    rw [← Functor.map_comp_assoc,
      rightDerivedFunctorUnit_app_comp_rightDerivedFunctorCompIso'_inv_app,
      pasteTwoSquaresIso_inv_app]
    have hn₁ := (rightDerivedCoeffIso e₂ h₂).inv.naturality
      (F₁'.rightDerivedFunctorUnit.app X)
    have hn₂ := rE.mapDerivedCategoryFactorsh.inv.naturality
      ((NatTrans.mapHomotopyCategory e'.inv (ComplexShape.up ℤ)).app
          X ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F₁' ⋙ F₂')) (ComplexShape.up ℤ)).inv.app
          X)
    simp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂
    rw [Functor.map_comp rE.mapDerivedCategory, Category.assoc, ← reassoc_of% hn₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn₁,
      reassoc_of% rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_inv_app,
      ← Functor.map_comp, ← Functor.map_comp,
      rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_inv_app,
      reassoc_of% rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_inv_app]
    have hn₃ : F₂.rightDerivedFunctorUnit.app ((rD.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((F₁'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
        F₂.rightDerivedFunctor.map (DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e₁.hom (ComplexShape.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (rC ⋙ F₁)) (ComplexShape.up ℤ)).inv.app
              X)) =
      DerivedCategory.Qh.map ((F₂.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory e₁.hom (ComplexShape.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (rC ⋙ F₁)) (ComplexShape.up ℤ)).inv.app
              X)) ≫
        F₂.rightDerivedFunctorUnit.app _ :=
      (F₂.rightDerivedFunctorUnit.naturality _).symm
    have hn₄ := (F₁.rightDerivedFunctorCompIso' F₂ e).inv.naturality
      (rC.mapDerivedCategoryFactorsh.inv.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hn₄
    rw [Functor.map_comp F₂.rightDerivedFunctor, reassoc_of% hn₃, hn₄,
      reassoc_of% rightDerivedFunctorUnit_app_comp_rightDerivedFunctorCompIso'_inv_app]
    simp only [← Functor.map_comp_assoc]
    congr 1
    · congr 1
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      simp only [mapHomotopyCategoryCompIso_refl_inv_app, Category.comp_id,
        NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
      congr 1
      ext n
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        Functor.mapHomologicalComplex_map_f, ← hcomp, Category.assoc]
      erw [Iso.hom_inv_id_app, Category.comp_id]
      rfl
    · simp
  intro K
  have h := NatTrans.congr_app key K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  exact (Iso.inv_eq_inv ((pasteTwoSquaresIso _ _).app K ≪≫ rE.mapDerivedCategory.mapIso
    ((Functor.rightDerivedFunctorCompIso' F₁' F₂' e').app K))
    ((Functor.rightDerivedFunctorCompIso' F₁ F₂ e).app _ ≪≫ (rightDerivedCoeffIso eH hH).app K)).mp
    (by simpa using h)

end CoeffComp

section SquareIso

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- A variant of `Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj` with the comparisons of
the target moved to the right hand side. -/
lemma mapDerivedCategorySquareIso_hom_app_Qh_obj' (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app X) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (ComplexShape.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (ComplexShape.up ℤ)).inv.app
              X) ≫
        G₂.mapDerivedCategoryFactorsh.inv.app ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.inv.app X) := by
  rw [← Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj e X]
  simp [← Functor.map_comp]

end SquareIso

section Unit

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D] [HasDerivedCategory D']
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions D']
  {rC : C' ⥤ C} {rD : D' ⥤ D} [rC.Additive] [PreservesFiniteLimits rC]
  [PreservesFiniteColimits rC] [rD.Additive] [PreservesFiniteLimits rD]
  [PreservesFiniteColimits rD] {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']

/-- The units of the derived adjunctions `D(L) ⊣ RR` and `D(L') ⊣ RR'` are compatible with the
coefficient comparisons, provided the units of `L ⊣ R` and `L' ⊣ R'` are. -/
lemma coeffCompatible_mapDerivedCategoryRightDerivedAdjunction_unit (adj : L ⊣ R)
    (adj' : L' ⊣ R') (eL : rC ⋙ L ≅ L' ⋙ rD) (eR : R' ⋙ rC ≅ rD ⋙ R)
    (hR : ∀ (K : CochainComplex D' ℤ) [K.IsKInjective], IsIso (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((rD.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (hη : ∀ X : C', rC.map (adj'.unit.app X) ≫ eR.hom.app (L'.obj X) =
      adj.unit.app (rC.obj X) ≫ R.map (eL.hom.app X)) :
    CoeffCompatible
      (Functor.rightUnitor rC.mapDerivedCategory ≪≫ (Functor.leftUnitor rC.mapDerivedCategory).symm)
      (pasteTwoSquaresIso (Functor.mapDerivedCategorySquareIso eL) (rightDerivedCoeffIso eR hR))
      adj.mapDerivedCategoryRightDerivedAdjunction.unit
      adj'.mapDerivedCategoryRightDerivedAdjunction.unit := by
  have key : Functor.whiskerRight adj'.mapDerivedCategoryRightDerivedAdjunction.unit
        rC.mapDerivedCategory =
      Functor.whiskerLeft rC.mapDerivedCategory adj.mapDerivedCategoryRightDerivedAdjunction.unit ≫
        (pasteTwoSquaresIso (Functor.mapDerivedCategorySquareIso eL)
          (rightDerivedCoeffIso eR hR)).hom := by
    refine Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ)) (fun X ↦ ?_)
    have hη' : adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
        R'.rightDerivedFunctor.map (L'.mapDerivedCategoryFactorsh.hom.app X) =
        DerivedCategory.Qh.map ((adj'.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X) ≫
          R'.rightDerivedFunctorUnit.app ((L'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) :=
      (adj'.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
        (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ)) L'.mapDerivedCategoryFactorsh.hom
        R'.rightDerivedFunctorUnit X
    have hη₀ : adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Qh.obj ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app
          ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
            ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
          R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
      (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
        R.rightDerivedFunctorUnit _
    have hnat := adj.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
      (rC.mapDerivedCategoryFactorsh.inv.app X)
    simp only [Functor.id_map, Functor.comp_map] at hnat
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      pasteTwoSquaresIso_hom_app]
    have hη₁ : adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Qh.obj ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
            ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
          R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
          R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app
            ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) := by
      rw [← cancel_mono (R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app
        ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X))), hη₀]
      simp [← Functor.map_comp]
    have hη₁' : adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj X) =
        DerivedCategory.Qh.map ((adj'.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X) ≫
          R'.rightDerivedFunctorUnit.app ((L'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
          R'.rightDerivedFunctor.map (L'.mapDerivedCategoryFactorsh.inv.app X) := by
      rw [← cancel_mono (R'.rightDerivedFunctor.map (L'.mapDerivedCategoryFactorsh.hom.app X)),
        hη']
      simp [← Functor.map_comp]
    have hn := (rightDerivedCoeffIso eR hR).hom.naturality
      (L'.mapDerivedCategoryFactorsh.inv.app X)
    have hβ : R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((rC.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
        R.rightDerivedFunctor.map (DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory eL.hom (ComplexShape.up ℤ)).app X)) =
      DerivedCategory.Qh.map ((R.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory eL.hom (ComplexShape.up ℤ)).app X)) ≫
        R.rightDerivedFunctorUnit.app ((rD.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((L'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
      (R.rightDerivedFunctorUnit.naturality _).symm
    have hf := rC.mapDerivedCategoryFactorsh.inv.naturality
      ((adj'.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hn hf
    rw [← cancel_epi (rC.mapDerivedCategoryFactorsh.inv.app X), reassoc_of% hnat, hη₁, hη₁']
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc (F := R.rightDerivedFunctor),
      ← Functor.map_comp_assoc (F := R.rightDerivedFunctor), Category.assoc,
      mapDerivedCategorySquareIso_hom_app_Qh_obj']
    simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp, Category.comp_id,
      Functor.map_comp, Category.assoc]
    rw [hn, reassoc_of% hβ,
      reassoc_of% rightDerivedFunctorUnit_app_comp_rightDerivedCoeffIso_hom_app, ← reassoc_of% hf]
    simp only [← Functor.map_comp_assoc (F := DerivedCategory.Qh)]
    congr 1
    congr 1
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Functor.comp_obj,
      Category.id_comp,
      Adjunction.mapHomotopyCategory_unit_app_quotient, NatTrans.mapHomotopyCategory_app,
      Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    erw [Adjunction.mapHomotopyCategory_unit_app_quotient (ComplexShape.up ℤ) adj
      ((rC.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
    rw [← Functor.map_comp]
    congr 1
    ext n
    simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f]
    erw [← reassoc_of% (hη (K.X n)), Iso.hom_inv_id_app, Category.comp_id]
  intro K
  simpa using NatTrans.congr_app key K

end Unit

/-- `derivedRestrictScalarsCompRightDerivedLowerStarIso` is an instance of
`rightDerivedCoeffIso`. -/
lemma derivedRestrictScalarsCompRightDerivedLowerStarIso_eq_rightDerivedCoeffIso
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd =
      rightDerivedCoeffIso (lowerStarCompRestrictScalarsIso ρ f)
        (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ f d hd K) :=
  rfl

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- The base change comparison `(c.i)_! ⟶ (d.i)_! ⋙ (r.hom)^*` of a refinement is compatible
with the coefficient comparisons. -/
lemma coeffCompatible_refinement_openImmersionLowerShriekBaseChange {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d) :
    haveI := c.isOpenImmersion
    haveI := d.isOpenImmersion
    CoeffCompatible (openImmersionLowerShriekRestrictScalarsIso ρ c.i)
      (pasteTwoSquaresIso (openImmersionLowerShriekRestrictScalarsIso ρ d.i)
        (upperStarRestrictScalarsIso ρ r.hom))
      (r.openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ))
      (r.openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} Λ')) := by
  have := c.isOpenImmersion
  have := d.isOpenImmersion
  intro K
  have h := coeffCompatible_openImmersionLowerShriekBaseChangeMap ρ
    (⟨by simp [r.i_hom]⟩ : CommSq (𝟙 X) c.i d.i r.hom) K
  rw [openImmersionLowerShriekBaseChangeMap_id_left _ c.i r.hom d.i r.i_hom,
    openImmersionLowerShriekBaseChangeMap_id_left _ c.i r.hom d.i r.i_hom] at h
  have hid := NatTrans.congr_app (upperStarRestrictScalarsIso_id_hom ρ X) K
  have hn := (openImmersionLowerShriekRestrictScalarsIso ρ c.i).hom.naturality
    ((upperStarId _ X).hom.app K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Functor.id_obj,
    Category.comp_id] at hid
  erw [Category.comp_id] at hid
  simp only [Functor.comp_map] at hn
  simp only [pasteTwoSquaresIso_hom_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.id_obj, Functor.comp_obj, Category.id_comp,
    Functor.map_comp, Category.assoc, ← reassoc_of% hn] at h
  rw [← Functor.map_comp_assoc, hid] at h
  rw [pasteTwoSquaresIso_hom_app]
  exact (cancel_epi _).1 h

variable [Finite Λ] [Finite Λ'] {X Y : Scheme.{u}} {f : X ⟶ Y} [CompactSpace Y]

omit [Finite Λ'] in
/-- The comparison of derived lower shrieks along a refinement of compactifications is
compatible with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison
    {c d : Compactification f} (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    CoeffCompatible (compactificationRestrictScalarsIso ρ d)
      (compactificationRestrictScalarsIso ρ c)
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ) r hcart)
      (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ') r hcart) := by
  have := c.isOpenImmersion
  have := d.isOpenImmersion
  have := c.isProper
  have := d.isProper
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  obtain ⟨dq, hdq⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite r.hom
  obtain ⟨dd, hdd⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite d.g
  obtain ⟨dc, hdc⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite c.g
  have hU := coeffCompatible_mapDerivedCategoryRightDerivedAdjunction_unit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') r.hom)
    (upperStarRestrictScalarsIso ρ r.hom) (lowerStarCompRestrictScalarsIso ρ r.hom)
    (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ r.hom dq hdq K)
    (fun M ↦ by
      simpa [lowerStarCompRestrictScalarsIso, upperStarRestrictScalarsIso] using
        restrictScalars_map_unit_app ρ r.hom M)
  have hB : CoeffCompatible (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ d.i)
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ r.hom)))
      (refinementLowerShriekBaseChangeDerivedIso _ r hcart).hom
      (refinementLowerShriekBaseChangeDerivedIso _ r hcart).hom :=
    (CoeffCompatible.mapDerivedCategoryNatIso
      (β := @asIso _ _ _ _ _ (r.isIso_openImmersionLowerShriekBaseChange _ hcart))
      (β' := @asIso _ _ _ _ _ (r.isIso_openImmersionLowerShriekBaseChange _ hcart))
      (coeffCompatible_refinement_openImmersionLowerShriekBaseChange ρ r)).comp
      (CoeffCompatible.mapDerivedCategoryCompIso _ _)
  have hres (M : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
      (Sheaf.restrictScalars _ ρ).map
          ((lowerStarComp (ModuleCat.{u + 1} Λ') r.hom d.g).hom.app M) =
        (lowerStarComp (ModuleCat.{u + 1} Λ) r.hom d.g).hom.app
          ((Sheaf.restrictScalars _ ρ).obj M) := by
    ext V : 3
    rfl
  have hC := coeffCompatible_rightDerivedFunctorCompIso' (refinementLowerStarComp _ r)
    (refinementLowerStarComp _ r) (lowerStarCompRestrictScalarsIso ρ r.hom)
    (lowerStarCompRestrictScalarsIso ρ d.g) (lowerStarCompRestrictScalarsIso ρ c.g)
    (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ r.hom dq hdq K)
    (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ d.g dd hdd K)
    (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ c.g dc hdc K)
    (fun M ↦ by
      simp [lowerStarCompRestrictScalarsIso, refinementLowerStarComp, ← hres,
        ← Functor.map_comp_assoc, eqToHom_map])
  have h₁ :=
    (hU.whiskerLeft (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ d.i)).whiskerRight
    (rightDerivedCoeffIso (lowerStarCompRestrictScalarsIso ρ d.g)
      (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ d.g dd hdd K))
  have h₂ := hB.inv.whiskerRight (pasteTwoSquaresIso
    (rightDerivedCoeffIso (lowerStarCompRestrictScalarsIso ρ r.hom)
      (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ r.hom dq hdq K))
    (rightDerivedCoeffIso (lowerStarCompRestrictScalarsIso ρ d.g)
      (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ d.g dd hdd K)))
  have h₃ := hC.whiskerLeft (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
  refine (h₁.comp_of_eq (h₂.comp h₃) fun K ↦ ?_).of_hom_app_eq (fun K ↦ ?_) fun K ↦ rfl
  · simp [pasteTwoSquaresIso_hom_app]
  · simp [compactificationRestrictScalarsIso, pasteTwoSquaresIso_hom_app]
    rfl

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation

/-!
# Representation of left derived comparisons of exact functors

For an exact functor `F`, the total left derived functor `L(F)` is presented by `F` through the
compatibility isomorphism `L(F) ≅ D(F)`. The isomorphisms `Functor.leftDerivedFunctorNatIso` and
`Functor.leftDerivedFunctorCompIso` represent their defining ordinary data for these
presentations.

Source: Stacks Project, Tag 05RU (universal property of localization) and Tag 05S7.
-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open DerivedPresentation

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The presentation of the total left derived functor of an exact functor by the functor
itself, through `Functor.leftDerivedFunctorIsoMapDerivedCategory`. -/
noncomputable abbrev leftDerivedPresentation : DerivedPresentation F.leftDerivedFunctor F :=
  (ofMap F).ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm

lemma leftDerivedPresentation_hom_app (K : CochainComplex C ℤ) :
    (leftDerivedPresentation F).hom.app K =
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategoryFactors.hom.app K :=
  rfl

lemma derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_hom :
    DerivedRepresents (leftDerivedPresentation F) (ofMap F)
      F.leftDerivedFunctorIsoMapDerivedCategory.hom (𝟙 F) :=
  (DerivedRepresents.inv (τ := F.leftDerivedFunctorIsoMapDerivedCategory.symm)
    (τ₀ := Iso.refl F) (derivedRepresents_ofIso (ofMap F) _)).congr rfl rfl

lemma derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_inv :
    DerivedRepresents (ofMap F) (leftDerivedPresentation F)
      F.leftDerivedFunctorIsoMapDerivedCategory.inv (𝟙 F) :=
  derivedRepresents_ofIso (ofMap F) _

/-- `Functor.leftDerivedFunctorNatIso e` represents `e`. -/
lemma derivedRepresents_leftDerivedFunctorNatIso {G : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    DerivedRepresents (leftDerivedPresentation F) (leftDerivedPresentation G)
      (F.leftDerivedFunctorNatIso e).hom e.hom :=
  (((derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_hom F).comp
    (derivedRepresents_mapDerivedCategoryNatIso e)).comp
    (derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_inv G)).congr
      (by simp [leftDerivedFunctorNatIso]) (by simp)

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- `Functor.leftDerivedFunctorCompIso` represents the identity of `F ⋙ G`. -/
lemma derivedRepresents_leftDerivedFunctorCompIso (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedRepresents (leftDerivedPresentation (F ⋙ G))
      ((leftDerivedPresentation F).comp (leftDerivedPresentation G))
      (F.leftDerivedFunctorCompIso G).hom (𝟙 (F ⋙ G)) :=
  ((((derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_hom (F ⋙ G)).comp
    (derivedRepresents_mapDerivedCategoryCompIso F G)).comp
    ((derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_inv F).whiskerRight
      (ofMap G))).comp
    ((derivedRepresents_leftDerivedFunctorIsoMapDerivedCategory_inv G).whiskerLeft
      (leftDerivedPresentation F))).congr
      (by simp [leftDerivedFunctorCompIso]) (by simp)

end Composition

end CategoryTheory.Functor

/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Associativity
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Composition of the transition maps of derived pushforwards

The transition maps `Rh_* K ⟶ Rh'_* (a^* K)` of `AlgebraicGeometry.Etale.lowerStarPlusTransition`
attached to triangles `a ≫ h = h'` are natural in `K`, compose along `Y₂ ⟶ Y₁ ⟶ Y` up to the
composition isomorphism of the derived pullbacks, and are isomorphisms along universal
homeomorphisms `a` (for instance thickenings), since then the derived pullback along `a` is
fully faithful.

## Main statements

- `AlgebraicGeometry.Etale.lowerStarPlusTransition_naturality`: naturality.
- `AlgebraicGeometry.Etale.lowerStarPlusTransition_comp`: the cocycle condition.
- `AlgebraicGeometry.Etale.isIso_lowerStarPlusTransition`: the transition map along a
  universal homeomorphism is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]

/-- The functor induced on the bounded below derived categories by an additive equivalence of
abelian categories is faithful. -/
lemma faithful_mapDerivedCategoryPlus [F.IsEquivalence] : F.mapDerivedCategoryPlus.Faithful :=
  have : (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι).Faithful :=
    Functor.Faithful.of_iso F.mapDerivedCategoryPlusCompatibility.symm
  Functor.Faithful.of_comp _ DerivedCategory.Plus.ι

/-- The functor induced on the bounded below derived categories by an additive equivalence of
abelian categories is full. -/
lemma full_mapDerivedCategoryPlus [F.IsEquivalence] : F.mapDerivedCategoryPlus.Full :=
  have : (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι).Full :=
    Functor.Full.of_iso F.mapDerivedCategoryPlusCompatibility.symm
  Functor.Full.of_comp_faithful _ DerivedCategory.Plus.ι

end CategoryTheory.Functor

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Transition

variable {X Y Y₁ Y₂ : Scheme.{u}}

/-- The transition map of a triangle `a ≫ h = h₁`, written with the composition isomorphism
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` along the diagonal `h₁`. -/
lemma Etale.lowerStarPlusTransition_eq (a : Y₁ ⟶ Y) (h : Y ⟶ X) (h₁ : Y₁ ⟶ X)
    (w : a ≫ h = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a h h₁ w K =
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h₁).unit.app
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h h₁ w.symm).hom.app
              (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
            D+((a)^*[ModuleCat.{u + 1} Λ]).map
              ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app
                K)) := by
  subst w
  rw [Etale.lowerStarPlusTransition, eqToIso_refl, Iso.refl_trans]
  rfl

/-- The transition maps of derived pushforwards are natural in the complex. -/
@[reassoc]
lemma Etale.lowerStarPlusTransition_naturality (a : Y₁ ⟶ Y) (h : Y ⟶ X) (h₁ : Y₁ ⟶ X)
    (w : a ≫ h = h₁)
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫ Etale.lowerStarPlusTransition Λ a h h₁ w L =
      Etale.lowerStarPlusTransition Λ a h h₁ w K ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  rw [Etale.lowerStarPlusTransition_eq, Etale.lowerStarPlusTransition_eq]
  rw [Category.assoc]
  exact Adjunction.map_unit_app_comp_map_comp_counit
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h₁) _ f

/-- **The cocycle condition for the transition maps.** For `a₂ : Y₂ ⟶ Y₁` and `a₁ : Y₁ ⟶ Y`
over `X`, the transition map along `a₁₂ = a₂ ≫ a₁` followed by the composition isomorphism
`a₁₂^* ≅ a₁^* ⋙ a₂^*` is the transition map along `a₁` followed by the one along `a₂`. -/
lemma Etale.lowerStarPlusTransition_comp (a₁ : Y₁ ⟶ Y) (a₂ : Y₂ ⟶ Y₁) (a₁₂ : Y₂ ⟶ Y)
    (ha : a₁₂ = a₂ ≫ a₁) (h : Y ⟶ X) (h₁ : Y₁ ⟶ X) (h₂ : Y₂ ⟶ X) (w₁ : a₁ ≫ h = h₁)
    (w₂ : a₂ ≫ h₁ = h₂) (w₁₂ : a₁₂ ≫ h = h₂)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a₁₂ h h₂ w₁₂ K ≫
        R+((h₂)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ a₁ a₁₂ ha).hom.app K) =
      Etale.lowerStarPlusTransition Λ a₁ h h₁ w₁ K ≫
        Etale.lowerStarPlusTransition Λ a₂ h₁ h₂ w₂ (D+((a₁)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  rw [Etale.lowerStarPlusTransition_eq, Etale.lowerStarPlusTransition_eq,
    Etale.lowerStarPlusTransition_eq]
  exact Adjunction.unit_app_comp_map_comp_counit_comp _ _ _ _ _ _ _
    (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ) a₂ a₁ h a₁₂ h₁ h₂ ha w₁.symm
      (by rw [← w₁₂]) (by rw [← w₂])).symm K

/-- The transition map along a universal homeomorphism `a` (for instance a thickening) is an
isomorphism: the pullback along `a` is an equivalence of categories of étale sheaves, so the
unit of the derived adjunction `La^* ⊣ Ra_*` is an isomorphism. -/
lemma Etale.isIso_lowerStarPlusTransition (a : Y₁ ⟶ Y) [IsUniversalHomeomorphism a]
    (h : Y ⟶ X) (h₁ : Y₁ ⟶ X) (w : a ≫ h = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (Etale.lowerStarPlusTransition Λ a h h₁ w K) := by
  have : ((a)^*[ModuleCat.{u + 1} Λ]).IsEquivalence :=
    Etale.isEquivalence_upperStar (ModuleCat.{u + 1} Λ) a
  have := Functor.full_mapDerivedCategoryPlus ((a)^*[ModuleCat.{u + 1} Λ])
  have := Functor.faithful_mapDerivedCategoryPlus ((a)^*[ModuleCat.{u + 1} Λ])
  rw [Etale.lowerStarPlusTransition_eq]
  exact Adjunction.isIso_unit_app_comp_map_comp_counit _
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a) _
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h h₁ w.symm) K

end Transition

end AlgebraicGeometry

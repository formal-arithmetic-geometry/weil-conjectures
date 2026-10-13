/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit

/-! # Higher direct image transition compatibility

Source: Stacks Project, Tags 09Z1 and 03Q8, canonical comparison maps.
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Transitions compose for the canonical pullback coefficients.
Source: Stacks Tag 09Z1, canonical comparisons; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-core-composition).

Proof: use the derived transition composition identity at F[0], then apply homology.
The derived identity follows by applying the inverse h'' adjunction hom-set equivalence:
naturality moves the first transition inside b^*, the h' counit cancels the h' unit,
and associativity of derived pullback comparisons identifies the remaining adjunct
with the one for b≫a. The two degree-zero comparisons compose to the ordinary pullback
comparison, as checked degreewise on the single complex and preserved by localization.
Thus homology gives precisely the displayed comparison. Identity morphisms give the
unit law and zero sheaves give zero maps; no properness or degree bound is required.
-/
theorem higher_direct_image_transition_core_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' Y'' : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImageTransition Λ (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) b a).hom.app F))) =
      higherDirectImageTransition Λ a h h' wa q F ≫
        higherDirectImageTransition Λ b h' h'' wb q
          (((a)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  have hc := lowerStarPlusTransition_comp Λ a b (b ≫ a) rfl h h' h'' wa wb
    (by rw [Category.assoc, wa, wb]) ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have hs := upperStarCompDerivedPlus_hom_app_singleFunctor Λ b a (b ≫ a) rfl F
  have hs' : (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b a (b ≫ a) rfl).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (((b ≫ a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) b a (b ≫ a) rfl).hom.app F) =
      D+((b)^*[ModuleCat.{u + 1} Λ]).map
        ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      (((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((a)^*[ModuleCat.{u + 1} Λ]).obj F) := by
    rw [← hs, Iso.inv_hom_id_app_assoc]
  simp only [higherDirectImageTransition, ← Functor.map_comp, Category.assoc]
  congr 1
  rw [reassoc_of% (lowerStarPlusTransition_naturality Λ b h' h'' wb
    ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)), ← hc]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hs']

end AlgebraicGeometry.Etale

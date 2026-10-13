/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

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
          (((a)^*[ModuleCat.{u + 1} Λ]).obj F) := by sorry

end AlgebraicGeometry.Etale

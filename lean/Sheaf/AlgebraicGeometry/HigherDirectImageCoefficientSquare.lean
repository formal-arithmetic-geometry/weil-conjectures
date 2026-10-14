/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower
import Sheaf.AlgebraicGeometry.HigherDirectImageTransitionComposition

/-! # Higher-image transitions around a coefficient square

Source: Stacks Project Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-higher-image-coefficient-square)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] lowerStarPlusTransition

variable (Λ : Type (u + 1)) [CommRing Λ]


private theorem composition_of_eq
    {X Y Y' Y'' : Scheme.{u}} (a : Y' ⟶ Y) (b : Y'' ⟶ Y')
    (h : Y ⟶ X) (h' : Y' ⟶ X) (h'' : Y'' ⟶ X)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'')
    (m : Y'' ⟶ Y) (wm : m = b ≫ a)
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F' : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F'' : Sheaf Y''.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : ((a)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ F')
    (g : ((b)^*[ModuleCat.{u + 1} Λ]).obj F' ⟶ F'') :
    higherDirectImageTransition Λ m h h'' (by rw [wm, Category.assoc, wa, wb]) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) b a m wm).hom.app F ≫
          ((b)^*[ModuleCat.{u + 1} Λ]).map f ≫ g))) =
      (higherDirectImageTransition Λ a h h' wa q F ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f))) ≫
      (higherDirectImageTransition Λ b h' h'' wb q F' ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map g))) := by
  subst m
  exact higher_direct_image_transition_composition Λ a b h h' h'' wa wb q
    F F' F'' f g

/-- A commuting square of triangles gives equal higher-image maps whenever its
underived coefficient square commutes.

Source: Stacks Project Tag 09Z1, canonical restriction maps; the mate-pasting step
of lem-sbc-target-sheaf-comparison-naturality.
(blueprint: lem-sbc-higher-image-coefficient-square)

Proof: Compose the higher-image transitions along a followed by cU using
higher_direct_image_transition_composition, with coefficient maps d and fU.
Compose along cV followed by b using the same law, with coefficient maps fV and e.
Both routes are the transition along the composite map to YV. The equation ws
identifies these maps; the upperStarComp with this named composite records the
required transport. The hypothesis wc identifies the two coefficient suffixes.
Apply the single functor, RhZU_* and degree-q homology to that equality and paste
it with the two composition identities. This proves the square without requiring
any arrow to be an isomorphism, any sheaf to be nonzero, or q to be nonnegative. -/
theorem higherDirectImage_coefficient_square
    {X YV YU ZV ZU : Scheme.{u}}
    (a : YU ⟶ YV) (b : ZU ⟶ ZV) (cV : ZV ⟶ YV) (cU : ZU ⟶ YU)
    (hV : YV ⟶ X) (hU : YU ⟶ X) (kV : ZV ⟶ X) (kU : ZU ⟶ X)
    (wa : a ≫ hV = hU) (wb : b ≫ kV = kU)
    (wV : cV ≫ hV = kV) (wU : cU ≫ hU = kU)
    (ws : cU ≫ a = b ≫ cV) (q : ℤ)
    (FV : Sheaf YV.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (FU : Sheaf YU.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (GV : Sheaf ZV.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (GU : Sheaf ZU.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (d : ((a)^*[ModuleCat.{u + 1} Λ]).obj FV ⟶ FU)
    (fV : ((cV)^*[ModuleCat.{u + 1} Λ]).obj FV ⟶ GV)
    (fU : ((cU)^*[ModuleCat.{u + 1} Λ]).obj FU ⟶ GU)
    (e : ((b)^*[ModuleCat.{u + 1} Λ]).obj GV ⟶ GU)
    (wc : (upperStarComp (ModuleCat.{u + 1} Λ) cU a).hom.app FV ≫
        ((cU)^*[ModuleCat.{u + 1} Λ]).map d ≫ fU =
      (upperStarComp (ModuleCat.{u + 1} Λ) b cV (cU ≫ a) ws).hom.app FV ≫
        ((b)^*[ModuleCat.{u + 1} Λ]).map fV ≫ e) :
    (higherDirectImageTransition Λ a hV hU wa q FV ≫
      higherDirectImageMap Λ hU q d) ≫
      (higherDirectImageTransition Λ cU hU kU wU q FU ≫
        higherDirectImageMap Λ kU q fU) =
    (higherDirectImageTransition Λ cV hV kV wV q FV ≫
      higherDirectImageMap Λ kV q fV) ≫
      (higherDirectImageTransition Λ b kV kU wb q GV ≫
        higherDirectImageMap Λ kU q e) := by
  have hh :
    (higherDirectImageTransition Λ a hV hU wa q FV ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((hU)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map d))) ≫
      (higherDirectImageTransition Λ cU hU kU wU q FU ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((kU)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map fU))) =
    (higherDirectImageTransition Λ cV hV kV wV q FV ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((kV)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map fV))) ≫
      (higherDirectImageTransition Λ b kV kU wb q GV ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((kU)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map e))) := by
    have ha := higher_direct_image_transition_composition Λ a cU hV hU kU wa wU q
      FV FU GU d fU
    have hb := composition_of_eq Λ cV b hV kV kU wV wb (cU ≫ a) ws q
      FV GV GU fV e
    apply ha.symm.trans
    apply Eq.trans _ hb
    exact congrArg (fun z ↦
      higherDirectImageTransition Λ (cU ≫ a) hV kU
        (by rw [Category.assoc, wa, wU]) q FV ≫
          (DerivedCategory.Plus.homologyFunctor _ q).map
            (R+((kU)_*[ModuleCat.{u + 1} Λ]).map
              ((DerivedCategory.Plus.singleFunctor _ 0).map z))) wc
  bc_structural_exact hh

end AlgebraicGeometry.Etale

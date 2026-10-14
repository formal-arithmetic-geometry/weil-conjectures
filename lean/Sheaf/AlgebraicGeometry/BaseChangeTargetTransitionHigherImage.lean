/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower
import Sheaf.AlgebraicGeometry.EtalePullbackSingleComp

/-! # Single-complex normalization of target transitions

Source: Stacks Project Tags 0F07 and 09Z1.
(blueprint: lem-sbc-target-transition-higher-image)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] lowerStarPlusTransition

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Normalize a target transition as a higher-image transition with an underived coefficient map.

Source: Stacks Project Tag 0F07, coefficient identification preceding condition (2),
and Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-target-transition-higher-image)

Proof: Expand the target transition before homology and the two instances of
baseChangeTargetFunctorIso. Naturality of the lower-star triangle transition moves
its source single-complex comparison to the target. The composition law for exact
pullbacks on single complexes identifies the two derived composition comparisons
with singleFunctor applied to the underived square comparison. Transport along wa
is respected by functoriality and proof irrelevance. The remaining target
single-complex comparison is the targetFunctorIso prefix. Apply Rh'_* and degree-q
homology, which preserve composition. Identity arrows and zero sheaves satisfy the
same identities; no sign or finiteness assumption on q is used. -/
theorem baseChangeTargetTransition_higherImage
    {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : ((π)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ F') :
    baseChangeTargetTransition Λ e h q π a e' h' wa wh F ≫
      (baseChangeTargetFunctor Λ e' h' q).map f ≫
      (baseChangeTargetFunctorHigherImageIso Λ e' h' q F').hom =
    (baseChangeTargetFunctorHigherImageIso Λ e h q F).hom ≫
      higherDirectImageTransition Λ a h h' wh q (((e)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      higherDirectImageMap Λ h' q
        ((upperStarComp (ModuleCat.{u + 1} Λ) a e).inv.app F ≫
          (upperStarComp (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app F ≫
          ((e')^*[ModuleCat.{u + 1} Λ]).map f) := by sorry

end AlgebraicGeometry.Etale

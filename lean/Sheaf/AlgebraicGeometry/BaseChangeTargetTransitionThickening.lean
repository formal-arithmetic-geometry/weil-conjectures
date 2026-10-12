/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

/-! # Target transition under a thickening

Source: Stacks Tags 03SI and 0F07, condition (1).
(blueprint: lem-sbc-target-transition-thickening)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A target transition above a thickening is an isomorphism.

Source: Stacks Tag 03SI and condition (1) in the proof of Tag 0F07.
(blueprint: lem-sbc-target-transition-thickening)

Proof: a base change of a thickening is a thickening: it is a closed immersion and
surjective on points. Pullback along a therefore gives an equivalence of étale sheaf
categories. The equivalence and its inverse are exact; applying them degreewise
and localizing at quasi-isomorphisms gives inverse equivalences on D+. Hence the
unit of the derived adjunction for a is invertible. Under `Rh'_* ≅ Rh_* Ra_*`, the
transition is `Rh_*` applied to this unit: expand the composite adjunction unit and
cancel the h-unit and h-counit by their triangle identity to recover its defining
mate formula. The remaining factors compare pullback along `a ≫ e` and `e' ≫ i`
using sq.w and compare sheaves placed in degree zero. They are isomorphisms, as
are their direct images. Apply degree-q homology, which preserves isomorphisms.
-/
theorem Etale.baseChangeTargetTransition_isIso_of_thickening
    {X T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e₂ : Y₂ ⟶ T₂) (h₂ : Y₂ ⟶ X) (q : ℤ)
    (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (a : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁) (h₁ : Y₁ ⟶ X)
    (sq : IsPullback a e₁ e₂ i) (wh : a ≫ h₂ = h₁)
    (F : Sheaf T₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeTargetTransition Λ e₂ h₂ q i a e₁ h₁ sq.w wh F) := by sorry

end AlgebraicGeometry

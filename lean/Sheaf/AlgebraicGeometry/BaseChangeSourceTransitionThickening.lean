/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition

/-! # Source transition under a thickening

Source: Stacks Tags 03SI and 0F07, condition (1).
(blueprint: lem-sbc-source-transition-thickening)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A source transition along a thickening is an isomorphism.

Source: Stacks Tag 03SI and condition (1) in the proof of Tag 0F07.
(blueprint: lem-sbc-source-transition-thickening)

Proof: pullback along the closed immersion surjective on points is an equivalence of
étale sheaf categories. An additive equivalence and its inverse are exact, so applying
both degreewise and localizing at quasi-isomorphisms gives inverse equivalences on D+.
Thus the unit of the derived adjunction for i is invertible. Under the canonical
identification `R(i ≫ g)_* ≅ Rg_* Ri_*`, the transition is `Rg_*` applied to this unit:
expand the composite adjunction unit and cancel the g-unit and g-counit using their
triangle identity. This agrees with the defining mate formula for the transition.
Pull back along p and apply degree-q homology. The comparison between the pullback
of a degree-zero complex and its pulled-back sheaf in degree zero is an isomorphism,
so every factor of the source transition is invertible.
-/
theorem Etale.baseChangeSourceTransition_isIso_of_thickening
    {X S T₁ T₂ : Scheme.{u}} (p : X ⟶ S) (g : T₂ ⟶ S) (q : ℤ)
    (i : T₁ ⟶ T₂) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (F : Sheaf T₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeSourceTransition Λ p g q i F) := by sorry

end AlgebraicGeometry

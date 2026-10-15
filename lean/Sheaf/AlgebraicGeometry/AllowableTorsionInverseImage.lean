/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE, SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Allowable torsion under inverse image

The inverse-image preservation lemma formerly private to
`BoundedBelowDerivedSmoothBaseChange`, shared with bounded smooth base change.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Inverse image preserves allowable torsion of abelian etale sheaves.
Source: blueprint sec-smooth-base-change/sk-rem-rest, allowable-output argument;
`BoundedBelowDerivedSmoothBaseChange.allowable_upperStar`
(blueprint: lem-sbc-allowable-torsion-upper-star).

Proof: at a geometric point s of U the inverse-image stalk is additively isomorphic
to the original stalk at s followed by f. Choose an allowable annihilator there.
The stalk comparison preserves natural-number scalar multiplication and zero and is
injective, so the same integer annihilates the given inverse-image stalk element. -/
theorem allowable_upperStar {U V : Scheme.{u}} (f : U ⟶ V) (P : Set ℕ)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : allowableTorsionSheafProperty V P F) :
    allowableTorsionSheafProperty U P ((upperStar AddCommGrpCat.{u + 1} f).obj F) := by
  intro Ω _ _ s x
  let j := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f s).app F
  obtain ⟨n, hn, hp, hx⟩ := hF Ω (s ≫ f) (j.hom.hom x)
  refine ⟨n, hn, hp, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso j.hom).1
  simpa only [map_nsmul, map_zero] using hx

end AlgebraicGeometry.Etale

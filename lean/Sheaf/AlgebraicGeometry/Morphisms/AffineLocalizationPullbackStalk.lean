/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Mathlib.AlgebraicGeometry.Stalk

/-! # Points and stalks of a coefficient-localized cartesian square -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A scheme base change along an affine localization preserves the stalk of every
point whose image avoids the denominators.

Source: the proof of lem-sbc-root-normalization-localization-comparison, step 3;
Mathlib localization prime correspondence and transitivity of localization.
(blueprint: lem-sbc-affine-localization-pullback-stalk)

Proof: On an affine neighborhood Spec D of x in X, the base change is the spectrum
of D localized at the image of M. The ideal of x is disjoint from these images,
since its contraction to R is the ideal of g(x). The localization prime
correspondence therefore supplies a prime x0 over x. Its local ring is obtained
by first localizing D at M and then at the extended prime. Transitivity of
localization identifies this with D localized at the original prime. Under the
canonical spectrum-stalk identifications this equivalence is precisely the stalk
map of the pullback projection. Transfer x0 and the invertibility of this map
through the affine-open inclusions and the given cartesian-square isomorphism.
Take e to be the inverse of that stalk map, followed by the equality c(x0)=x.
The square commutes, and the spectrum stalk map takes the germ of r to that
of its coefficient image. Naturality of composite stalk maps gives the displayed
identity for every r, before any special element is selected.
Empty spectra pose no exception: a supplied point x already rules them out. -/
theorem exists_lift_stalkEquiv_of_isLocalization
    (R S : CommRingCat.{u}) [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    {X Y : Scheme.{u}} (c : Y ⟶ X) (f : Y ⟶ Spec S) (g : X ⟶ Spec R)
    (hsq : IsPullback c f g (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (x : X) (hx : Disjoint (M : Set R) ((g x).asIdeal : Set R)) :
    ∃ x0 : Y, c x0 = x ∧
      ∃ e : Y.presheaf.stalk x0 ≃+* X.presheaf.stalk x,
        ∀ r : R,
          e ((f.stalkMap x0).hom
            (StructureSheaf.toStalk S (f x0) (algebraMap R S r))) =
              (g.stalkMap x).hom (StructureSheaf.toStalk R (g x) r) := by sorry

end AlgebraicGeometry.Scheme

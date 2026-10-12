/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant

/-!
# Locally constant direct image from finitely many universal-homeomorphism components

Source: smooth purity blueprint, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Direct image is locally constant when the source is a finite disjoint union of
open components each universally homeomorphic to the base.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, final paragraph;
steps 3 and 4 of `lem-weil-pbc-finite-map-generic-lisse-preservation`.
(blueprint: lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image).

Proof: Restrict E to each W i. These inverse images are lisse because pullback
preserves finite local constancy. The universal-homeomorphism equivalence of
small etale sites identifies each component direct image with inverse transport
through that equivalence. Transport a trivializing cover of the component sheaf.
Thus each component direct image has locally constant underlying set sheaf.
The sheaf condition for the disjoint component cover, pulled back to each
etale test object over Y, identifies f direct image E with the product of the
component direct images, naturally in the test object. Refine their finitely
many trivializing etale covers by a fibre product, and obtain a constant sheaf
on that cover. In the empty-family case X is empty by the cover hypothesis and
f direct image E is the zero abelian sheaf, whose underlying set sheaf is constant
singleton. Transport local constancy across the product identification. Finite
stalks are not asserted here: the caller proves them separately from the proved
finite-direct-image stalk formula. -/
theorem isLocallyConstant_finite_disjoint_universalHomeomorphism_directImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (W : Fin n → X.Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (hW : ∀ i, IsUniversalHomeomorphism ((W i).ι ≫ f))
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsLisseEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E)) := by sorry

end AlgebraicGeometry.Scheme

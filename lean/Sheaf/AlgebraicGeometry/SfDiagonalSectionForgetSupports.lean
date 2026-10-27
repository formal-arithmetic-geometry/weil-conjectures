/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Forgetting supports in the diagonal section map

This normalization involves only one self-product, with no change of coordinates.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the diagonal section
identification (blueprint: lem-sf-diagonal-section-forget-supports).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Forget-supports identifies the compact-support diagonal section map with the
composite of the two ordinary constant-object units, naturally in a map from
the tensor unit to any coefficient object on the original scheme.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the identification
M = Rp2_* Delta_* M, and lem-amb-p1-diagonal-integrals.proof.md, the diagonal
is a section for either projection.
(blueprint: lem-sf-diagonal-section-forget-supports).

Proof: put d = Delta and p = p_a, so d followed by p is identity.
Expand rightDerivedLowerShriekCompIso in its specified compatible tower:
use the chosen compactification of p and the compactification of d followed
by its open immersion obtained from the chosen compactification of d p.
In this tower the compositor is proper/open exchange followed by composition
of open extensions and composition of proper direct images. Substitute the
adjunction-mate formula for exchange. Naturality of the maps from open
extension to ordinary direct image, followed by the mate counit identity,
identifies the two forget-supports maps with the ordinary compositor.
The theorem rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar
in CompactificationRefinementLowerStar transports the tower calculation to
the chosen models for d and d p. Equivalently this is the calculation with
identity compactifications, where open extension is identity.
The identity comparison is, by definition,
forget-supports followed by the ordinary direct-image identity comparison.
Consequently the inverse identity/composition map used in diagonalUnit,
followed by the two forget-supports maps, is the inverse ordinary section
compositor. Under the constant-to-tensor-unit comparison, the ordinary section
compositor is the composite of the constant-object units for p and d: the
composition mate identity identifies it with the constant-object unit for
identity, which is identity because the constant-sheaf pullback comparisons
respect identity and composition. Naturality of proper forget-supports moves
the constant-to-tensor-unit comparison to the source. Postcompose this
normalization with Rp_* Rd_* of the map c.hom followed by theta, where
c is the constant-to-tensor-unit comparison. Naturality moves this map into
the diagonal direct image. The composite c.inv followed by c.hom is identity,
so functoriality leaves precisely theta inside the diagonal direct image on
the left. This gives the displayed formula for every coefficient object and
map theta, keeping that map intact.
The two Boolean cases use respectively diagonal_fst and diagonal_snd; no
projective-line isomorphism or base-change map is involved. The argument
applies unchanged to empty schemes and the zero coefficient ring. -/
theorem diagonalSection_forgetSupports
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (a : Bool)
    (K : DerivedCategoryModule A X)
    (θ : derivedTensorUnit (ModuleCat.{u + 1} A) X ⟶ K) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          ((ordinaryProperForgetComparison A
              (TraceDiagonalDatum.diagonal f)).hom.app
                (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
            (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map θ) ≫
        (ordinaryProperForgetComparison A
          (projection f a)).hom.app
            ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).obj K) =
      (constantUnit A X).inv ≫ supportedDerivedUnit A (projection f a) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
            ((constantUnit A X).hom ≫ θ)) := by sorry

end AlgebraicGeometry.Etale.SfP1Transport

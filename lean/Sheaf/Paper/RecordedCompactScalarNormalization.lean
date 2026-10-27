/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Paper.EtaleProEtaleCoefficientTransport
public import Sheaf.Paper.OpenScalarSiteCoherence
public import Sheaf.Paper.EtaleProEtaleScalarMateData

/-! # Fixed-module normalization of the recorded intrinsic coefficient arrow

Source: Stacks Project, Tags 00YV, 03D3 and 0GL6, and Step 3 of
lem-sp-transported-compact-scalar-site-square. This is a comparison of the two
pro-etale presentations only; no etale input or boundedness is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] transportedRecordedReductionDirectImageComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  pbcFixedScalarExtension DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

/-- The recorded intrinsic proper/open scalar arrow, after the prescribed realization
transport, is the fixed-module proper scalar mate followed by the image of the open
scalar comparison. This identifies an arrow on the entire pro-etale derived category.

Source: Stacks Project, more-etale.tex, Tag 0GL6 (proper/open coefficient comparison),
and Step 3 of lem-sp-transported-compact-scalar-site-square; the normalization argument
through the specified realization is agent-written.
(blueprint: lem-sp-recorded-compact-scalar-fixed-normalization).

Proof: apply the fully faithful realization functor at Y. Its image of the left
side is the defining conjugate of reductionDirectImageComparison. Expand that arrow
as the proper scalar mate followed by proper image of reductionOpenScalarIso.
Expand supportPresentation as the exact open realization comparison followed by
right-adjoint uniqueness and the K-injective-normalized direct-image realization.
Naturality moves the open realization comparison through the proper scalar mate.
Transpose the resulting proper square under the B-geometric adjunction. The
unit-preserving pullback coordinate change in directImagePresentation identifies
its counit with the fixed-module geometric counit. The section-identity scalar
restriction comparison defining scalarPresentation preserves the scalar units, so
the scalar/pullback mates have the same transpose in these coordinates. This proves
the proper-factor equality. For the open factor use the two open adjunctions:
reductionOpenModel is their left-adjoint uniqueness comparison, and
reductionOpenScalarIso is conjugation of the composite-left-adjoint uniqueness map.
Transpose along the open adjunction and then the scalar adjunction. Both paths are
the same sectionwise restriction comparison, since the realization unit cancels in
the definition of supportPresentation. Injectivity of these Hom bijections proves
the open-factor equality. Paste the two equalities and cancel the realization
unit/counit pairs. Faithfulness descends equality of the fixed-module maps; naturality
and extensionality give the equality of natural transformations. These arguments use
only adjunction identities, so zero coefficient rings, empty schemes, identity maps,
and unbounded inputs require no exceptions. No coefficient mate is inverted. -/
theorem recordedCompactScalar_fixed_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    transportedRecordedReductionDirectImageComparison φ c
        (reductionDirectImageComparison φ c.i c.g) =
      whiskerLeft
          (openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory
          (mateEquiv
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g)
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g)
            (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso (uliftRingHom φ) c.g).hom)).natTrans ≫
        whiskerRight (OpenScalarSite.scalarOpen (uliftRingHom φ) c.i).hom
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c.g).rightDerivedFunctor := by sorry

end AlgebraicGeometry.ProEtale.CoefficientCompatibility

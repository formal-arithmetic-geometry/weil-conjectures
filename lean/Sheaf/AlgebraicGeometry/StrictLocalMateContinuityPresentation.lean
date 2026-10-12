/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
public import Sheaf.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
import Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Presenting the strict-local mate as projection restriction

Source: Stacks Project, Tag 03Q9, the neighbourhood-colimit construction and the
injective-complex restriction maps in its final proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Present the source of the strict-local mate as neighbourhood hypercohomology,
and identify its germ components with projection pullbacks to the limit.
This supplies the input to derived continuity, without applying continuity and without
asserting that either the target cocone is a colimit or the mate is invertible.
Source: Stacks Project, Tag 03Q9, proof paragraphs 1 and 3; Tag 03Q8
(blueprint: lem-weil-pbc-strict-local-mate-continuity-presentation).

Proof: use the small representative category of affine pointed neighbourhoods of s.
It is cofiltered by strictHenselization_properties. Base change its diagram along f,
with limit the pullback of the strict henselization; the fibre-product limit theorem
and the characterisation of the structural map identify its cone legs. Its stages
are qcqs since the neighbourhoods are affine and f is qcqs; transitions are affine
since morphisms between affine schemes and their base changes are affine.
Take the diagram F of neighbourhood hypercohomology of the inverse images of K.
Choose a bounded-below injective representative J of K. Restriction along the etale
stage projections preserves injectives, so sections of J compute these groups, and
restriction of sections gives exactly the transition formula in the presentation.
By 03Q8 and invariance of geometric stalks under sheafification, the stalk of H^n Rf_*K
is the colimit of F. The canonical germ restriction is an isomorphism; exact inverse
image commutes with homology. Transport the stalk cocone through these two isomorphisms
to obtain sourceLegs and sourceIsColimit, with vertex the displayed source group.
Exact strict-local global sections and the Leray homology isomorphism identify the
displayed target with hypercohomology of the limit, giving limitIso. On J the
adjunction mate is restriction of sections along the pullback square. Thus each
source germ, followed by the mate and limitIso, is the projection pullback on
hypercohomology. This is precisely the restriction equation of the presentation.
This construction uses no continuity assertion and no isomorphism assertion for the mate.
It applies in negative degrees as well as positive degrees, and to the zero complex;
qcqs is used for the stages, not imposed on S or X separately. -/
theorem nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K)))) := by sorry

end AlgebraicGeometry.Etale

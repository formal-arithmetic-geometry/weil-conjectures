/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison

/-! # The derived mate on a neighbourhood germ -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The germ leg and derived mate agree with restriction of stage hypercohomology.
This identity stops before replacing derived restriction by termwise restriction:
that replacement is the separate theorem `injectiveSections_strictLocal_comparison`.
Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-injective-source-derived-restriction).

Proof: write M for the underlying complex of J. The right-derived unit identifies
Rf_*K with Q(f_*M), using q. Since f_*M is a bounded-below complex of injectives,
localization identifies a derived morphism from the free sheaf of a neighbourhood
with a Hom-complex cohomology class. Evaluating the free generator and restricting
along its etale pullback identifies this class with a class of stage sections;
the canonical map from these sections to derived sections is the stage factor
representativeSectionsComparison in the formula. The canonical germ map first
passes to homology and then takes the geometric germ of this same class.
The germ-leg characterization of strictHenselizationStalkRestriction, together
with Q.first, identifies this with restriction along the base cone leg.
Expand the derived mate as its adjunction unit, square comparison, and counit.
Naturality of the units and counits and the two triangle identities identify
its composite with that germ restriction with the derived adjunction unit along
Q.legs.app i. Q.over identifies the composite inverse image with the limit
projection. The resulting map to limit hypercohomology is therefore the derived
unit, Leray, and inverse composition comparison displayed on the right.
Exact inverse image commutes with homology; exact sections on the strict local
base and Leray supply the target transport strictLocalBaseChangeTargetIso.hom.
Naturality of localization and all these comparisons transports from M to K
along q. No acyclicity at the limit or continuity assertion is used. The argument
uses only functorial maps and adjunction identities, so also applies to zero
complexes, empty schemes, and every integer degree. -/
theorem strictLocalInjectiveSourceIso_derivedRestriction {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K))) ≫
        (strictLocalBaseChangeTargetIso f s K n).hom =
            (strictLocalInjectiveSourceIso f s K n J q i).hom ≫
              representativeSectionsComparison
                ((strictLocalNeighbourhoodProjection f s).app i) q n ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (Q.legs.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (Q.legs.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (pullback f (Scheme.strictHenselizationStructuralMap
        s)) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
        ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
        (Scheme.strictHenselizationStructuralMap s))
            (Q.over i).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i))).inv.app K.obj) := by sorry


end AlgebraicGeometry.Etale

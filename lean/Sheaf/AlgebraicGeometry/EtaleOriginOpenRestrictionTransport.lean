/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Comparison transport of the normalized open restriction map

Source: retained blueprint Step 7, restriction and mate-pasting calculation;
Stacks Tags 099R, 09AF and 09BN
(blueprint: lem-exc-etale-origin-open-restriction-transport).

This calculation concerns open restriction of a direct image, without any proper/open
interchange map or properness hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Exact comparison followed by canonical constant-ring realization.
Source: Stacks Tag 099R, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenComparison (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T ⥤ proEtaleDerivedCategory T A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- Canonical realization coordinates for exact open extension, descended termwise.
Source: Stacks Tags 00YV and 09AE, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
            (sfIntrinsicModuleEquivalence Y A).functor)) ≪≫
    mapDerivedCategoryCompIso _ _

/-- The termwise canonical open comparison in intrinsic constant coefficients.
Source: Stacks Tag 09AF, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenExtensionComparison {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        etaleOriginOpenComparison A Y ≅
      etaleOriginOpenComparison A X ⋙ sfIntrinsicDerivedOpen A j :=
  isoWhiskerRight
      ((mapDerivedCategoryCompIso _ _).symm ≪≫
        mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j) ≪≫
        mapDerivedCategoryCompIso _ _) (sfIntrinsicDerivedEquivalence Y A).functor ≪≫
    isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
      (etaleOriginOpenCoordinates A j).symm

/-- The counit-normalized direct-image comparison, included from D+ into D and then
transported by the canonical realization. Every compatibility isomorphism is the
published universal derived-functor comparison.
Source: Stacks Tag 099R, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A Y).obj
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj K.obj) ≅
      (proEtaleConstantDerivedDirectImage f A).obj
        ((etaleOriginOpenComparison A X).obj K.obj) :=
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let rp := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus (ULift.{u + 1, u} A) f
  (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    ((N Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app K).symm ≪≫
      ((N Y).mapDerivedCategoryPlusCompatibility.app (re.rightDerivedFunctorPlus.obj K)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (ProEtale.fixedComparisonDirectImageMatePlus
          (ULift.{u + 1, u} A) f)).app K) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((N X).mapDerivedCategoryPlus.obj K)) ≪≫
      rp.rightDerivedFunctor.mapIso ((N X).mapDerivedCategoryPlusCompatibility.app K)) ≪≫
    (sfIntrinsicDerivedDirectImageComparison f A).symm.app ((N X).mapDerivedCategory.obj K.obj)


attribute [local irreducible] etaleOriginOpenComparison etaleOriginOpenCoordinates
  etaleOriginOpenExtensionComparison etaleOriginOpenDirectImageComparison
  sfIntrinsicDerivedEquivalence sfIntrinsicModuleEquivalence sfIntrinsicExtensionByZero
  sfIntrinsicPullback exceptionalOpenAdjunction
  Etale.lowerStar Etale.upperStar Etale.openImmersionLowerShriek

/-- The open-restriction comparison is the mate of inverse open-extension comparison.
Source: Stacks Tag 09AF, the common-right-adjoint normalization
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenRestrictionMate {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        etaleOriginOpenComparison A X ⟶
      etaleOriginOpenComparison A Y ⋙ sfIntrinsicDerivedPullback A j :=
  (mateEquiv
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (exceptionalOpenAdjunction j A)
    (TwoSquare.mk _ _ _ _ (etaleOriginOpenExtensionComparison A j).inv)).natTrans

/-- Compare the direct image of an open extension, inserting the specified D+ inclusion
comparisons. Every factor is one of the fixed canonical comparisons.
Source: retained blueprint Step 7, final two arrows and their D+ coordinates
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenTargetComparison {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A T).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj)) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) :=
  let ke := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)
  let pe := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  (etaleOriginOpenComparison A T).mapIso
      (pe.rightDerivedFunctor.mapIso (ke.mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    etaleOriginOpenDirectImageComparison A p (ke.mapDerivedCategoryPlus.obj K) ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((etaleOriginOpenComparison A V).mapIso (ke.mapDerivedCategoryPlusCompatibility.app K) ≪≫
        (etaleOriginOpenExtensionComparison A (pullback.fst p i)).app K.obj)

/-- Canonical comparison carries inverse normalized etale open restriction to inverse
normalized intrinsic pro-etale open restriction. The assertion applies to any qcqs map,
any open immersion, and any bounded-below input; it does not use a proper/open interchange.
The etale isomorphism is fixed by its displayed exchange-and-inverse-unit formula.
Source: retained blueprint Step 7, restriction and mate-pasting calculation; Stacks
Tags 099R, 09AF and 09BN
(blueprint: lem-exc-etale-origin-open-restriction-transport).

Proof:
1. On sheaves, identify restriction of a direct image with direct image of restriction
   by evaluating on the same Cartesian fibre product. The constant scalar sections and
   their actions agree. The etale/pro-etale comparison and the intrinsic realization
   respect this section map, by their scalar-section normalization.
2. Restriction is right adjoint to exact open extension, so it preserves K-injectives.
   Derive the section square on K-injective representatives. The canonical comparison
   of direct images is its counit-normalized mate; uniqueness of right derivation gives
   the square with the specified D+ inclusion comparisons on its four edges.
3. The mate of inverse open-extension comparison is the canonical restriction
   comparison, by openComparison_unit_normalization. Exact termwise localization and
   canonical realization preserve this mate identity and both open units.
4. Apply the derived restriction square to the open extension of K. Replace its etale
   restriction followed by inverse open unit by lam.hom, using hlam. The corresponding
   pro-etale composite is the inverse of proEtaleOpenRestrictionLambdaInverse. Insert
   the unit equation from step 3 at the top open edge. Invert the two restriction
   isomorphisms and cancel their open units. The resulting square is the displayed
   equation, including all D+ compatibility factors in etaleOriginOpenTargetComparison.
   These calculations are natural and also apply to empty opens and the zero ring. -/
theorem etaleOriginOpenRestriction_transport {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (pullback.snd p i)] [QuasiSeparated (pullback.snd p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (lam :
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj)) ≅
      (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.obj
          K.obj)
    (hlam : lam.hom =
      (Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (IsPullback.of_hasPullback p i).toCommSq).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj) ≫
        (Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.map
            (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).unit.app K.obj))) :
    (etaleOriginOpenComparison A W).map lam.inv ≫
        (etaleOriginOpenRestrictionMate A i).app _ ≫
          (sfIntrinsicDerivedPullback A i).map (etaleOriginOpenTargetComparison A p i K).hom =
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).hom ≫
        (proEtaleOpenRestrictionLambdaInverse p i A).app
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj) := by
  sorry

end AlgebraicGeometry.Scheme

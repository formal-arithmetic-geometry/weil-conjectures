/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.Paper.UnboundedProperOpenInterchange
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.PbcActualRingedExchange
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.Paper.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Etale-origin proper/open interchange

Source: retained repaired proof of blueprint main-20261015,
`prop-exc-base-change-proper`, Step 7; Stacks Tags 099R and 0F7B
(blueprint: lem-exc-etale-origin-proper-open-interchange).

The five arrows use the published fixed-scalar comparisons, transported through the
canonical intrinsic realization. No ambient exceptional adjunction is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Exact comparison followed by canonical constant-ring realization.
Source: Stacks Tag 099R, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginOpenComparison (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T ⥤ proEtaleDerivedCategory T A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- Canonical realization coordinates for exact open extension, descended termwise.
Source: Stacks Tags 00YV and 09AE, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
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
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
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
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
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

/-- The specified etale interchange, selected together with its full representative and
open-adjunction normalization. Those conditions determine the map on all objects.
Source: Stacks Tag 0F7B, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginOpenEtaleInterchange {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)] :
    (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory ≅
    (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor :=
  (Etale.unboundedProperOpenInterchange (ULift.{u + 1, u} A)).choose_spec.choose
    (pullback.fst p i) (pullback.snd p i) p i (IsPullback.of_hasPullback p i).toCommSq


/-- The five-arrow site-transport composite. The two intervening Plus compatibility
isomorphisms merely identify termwise open extension before and after inclusion into D.
Source: retained blueprint Step 7, five-arrow display; Stacks Tags 099R and 0F7B
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginProperOpenIso {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicDerivedOpen A i).obj
        ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) :=
  let ke := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)
  let pe := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)
  (sfIntrinsicDerivedOpen A i).mapIso
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).symm ≪≫
    (etaleOriginOpenExtensionComparison A i).symm.app (re.rightDerivedFunctor.obj K.obj) ≪≫
    (etaleOriginOpenComparison A T).mapIso
      ((etaleOriginOpenEtaleInterchange A p i).app K.obj) ≪≫
    (etaleOriginOpenComparison A T).mapIso
      (pe.rightDerivedFunctor.mapIso (ke.mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    etaleOriginOpenDirectImageComparison A p (ke.mapDerivedCategoryPlus.obj K) ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((etaleOriginOpenComparison A V).mapIso (ke.mapDerivedCategoryPlusCompatibility.app K) ≪≫
        (etaleOriginOpenExtensionComparison A (pullback.fst p i)).app K.obj)

/-- Conjugation by the retained pair (K, alpha) specifying an etale origin. This is the
formula in the node, with no choice of witness made by the definition.
Source: retained blueprint Step 7, witness display; Stacks Tag 099R
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def witnessedEtaleOriginProperOpenIso {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)]
    {M : proEtaleDerivedCategory (pullback p i) A}
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (alpha : (etaleOriginOpenComparison A (pullback p i)).obj K.obj ≅ M) :
    (sfIntrinsicDerivedOpen A i).obj
        ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj M) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj M) :=
  (sfIntrinsicDerivedOpen A i).mapIso
      ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).mapIso alpha.symm) ≪≫
    etaleOriginProperOpenIso A p i K ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((sfIntrinsicDerivedOpen A (pullback.fst p i)).mapIso alpha)

/-- The already recorded restriction normalization, oriented as lambda rather than its
inverse. Its inverse is exactly the published open-unit followed by inverse restriction.
Source: retained blueprint Step 7, restriction display; Stacks Tags 09AE and 09BN
(blueprint: lem-exc-etale-origin-proper-open-interchange). -/
def etaleOriginOpenLambda {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsOpenImmersion i] :
    sfIntrinsicDerivedOpen A (pullback.fst p i) ⋙ proEtaleConstantDerivedDirectImage p A ⋙
        sfIntrinsicDerivedPullback A i ≅
      proEtaleConstantDerivedDirectImage (pullback.snd p i) A :=
  (@asIso _ _ _ _ (proEtaleOpenRestrictionLambdaInverse p i A)
    (proEtaleDerivedOpenRestriction p i A).2.2).symm

/-- Site transport preserves the canonical Cartesian proper/open interchange on every
bounded-below input of etale origin: invertibility, independence of the entire witness,
naturality for every morphism between witnessed objects, and both open-adjunction
normalizations. The first normalization includes the open unit identifying its source.
No ambient exceptional adjoint or all-sheaf finite-CD datum is a hypothesis.
Source: retained repaired blueprint proof of prop-exc-base-change-proper, Step 7;
Stacks Tags 099R and 0F7B (blueprint: lem-exc-etale-origin-proper-open-interchange).

Proof:
1. Base change makes r proper and k open. Proper maps are finite type and separated,
hence qcqs; exact open extensions descend all their comparison maps termwise.
2. The five factors are the inverse canonical mate b_r, inverse termwise e_i,
comparison pullback of the specified etale interchange, canonical mate b_p, and
Rp_* of e_k. Every factor is invertible; their naturality gives naturality in K.
3. Full faithfulness of comparison on D+ lifts the transition between two origin
witnesses to its unique etale isomorphism. Naturality of the five factors and cancellation
of the witness isomorphisms identify the two conjugates. The same argument for a general
morphism gives the stated naturality between arbitrary witnessed objects.
4. The counit equation for b_p and b_r, together with Cartesian pullback coherence,
identifies transported etale exchange with the ambient pro-etale exchange. The exact
unbounded etale exchange is the same unit-square-counit mate used in the normalization
of the specified etale interchange (def-kun-unbounded-exchange).
5. At each open edge the comparison e intertwines the open units
(lem-sf-open-comparison-unit-normalization); exactness passes that equation to complexes.
6. Compute restriction on a K-injective I: i^*p_*I=r_*k^*I, and k^*I remains K-injective.
Its r-adjunction transpose is Cartesian pullback followed by k^* of the p counit,
so the restriction normalization is precisely ambient exchange followed by inverse open
unit (lem-exc-proetale-derived-open-restriction).
7. Transpose the five factors under i_! adjoint to i^*. Insert the two open-unit
equations, the two direct-image counit equations and the Cartesian comparison. By the
transport-identifies-exchange identity the middle map is the exchange of step 6.
The etale interchange normalization therefore makes this transpose lambda inverse.
8. Uniqueness of transpose gives C=i_!(lambda inverse) followed by the open counit.
Conjugating by alpha and naturality preserve this equality. Apply i^* and use the
triangle identity to obtain the unit-normalized restriction equation. All objects and
operations are ordinary uncompleted constant-coefficient ones; only bounded-below etale
origin is used, with no constructibility or ambient-adjoint assumption. -/
theorem etaleOriginProperOpenInterchange (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsProper p] [IsOpenImmersion i]
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian W] [IsNoetherian (pullback p i)] :
    (∀ K, IsIso (etaleOriginProperOpenIso A p i K).hom) ∧
    ∀ (M : proEtaleDerivedCategory (pullback p i) A)
      (K : DerivedCategory.Plus
        (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (alpha : (etaleOriginOpenComparison A (pullback p i)).obj K.obj ≅ M),
      IsIso (witnessedEtaleOriginProperOpenIso A p i K alpha).hom ∧
      (∀ (L : DerivedCategory.Plus
          (Sheaf (pullback p i).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (beta : (etaleOriginOpenComparison A (pullback p i)).obj L.obj ≅ M),
        (witnessedEtaleOriginProperOpenIso A p i K alpha).hom =
          (witnessedEtaleOriginProperOpenIso A p i L beta).hom) ∧
      (∀ (N : proEtaleDerivedCategory (pullback p i) A)
        (L : DerivedCategory.Plus
          (Sheaf (pullback p i).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (beta : (etaleOriginOpenComparison A (pullback p i)).obj L.obj ≅ N) (f : M ⟶ N),
        (sfIntrinsicDerivedOpen A i).map
            ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).map f) ≫
          (witnessedEtaleOriginProperOpenIso A p i L beta).hom =
        (witnessedEtaleOriginProperOpenIso A p i K alpha).hom ≫
          (proEtaleConstantDerivedDirectImage p A).map
            ((sfIntrinsicDerivedOpen A (pullback.fst p i)).map f)) ∧
      ((exceptionalOpenAdjunction i A).unit.app
            ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj M) ≫
          (sfIntrinsicDerivedPullback A i).map
            (witnessedEtaleOriginProperOpenIso A p i K alpha).hom ≫
          (etaleOriginOpenLambda A p i).hom.app M = 𝟙 _) ∧
      ((witnessedEtaleOriginProperOpenIso A p i K alpha).hom =
        (sfIntrinsicDerivedOpen A i).map
            ((proEtaleOpenRestrictionLambdaInverse p i A).app M) ≫
          (exceptionalOpenAdjunction i A).counit.app
            ((proEtaleConstantDerivedDirectImage p A).obj
              ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme

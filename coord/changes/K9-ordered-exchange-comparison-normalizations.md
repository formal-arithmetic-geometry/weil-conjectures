# OrderedExchange coefficient normalization predicates and proof environment

## Reason

The original long complex equations are repeatedly elaborated in the unique-choice
definitions, causing per-file kernel timeouts. Name each unchanged equation as a
predicate, and expose its proof for the chosen comparison. No hypothesis or conclusion
changes after unfolding the predicate. Both unique choices and the limit-unit body
remain verbatim. The new definitions contain no `sorry` or arbitrary existence choice.

Also prune unused direct imports and use local opacity/instance priorities to prevent
unfolding fixed coefficient data while checking composites. These attributes are local
and do not change exported instance priorities or reducibility.

## Old

```lean
public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.Paper.PbcActualScalarPullback
public import Sheaf.Paper.PbcActualStrictPullback
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.Paper.StrictTowerOperations
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.CompletionMateComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.Paper.StrictTowerExchangeMateNormalization
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedToposMorphism
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

theorem rho_existsUnique (T : Scheme.{t}) :
    ∃! e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T,
      ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P) := by
  sorry

theorem lambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T,
      ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

def rawComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :=
  (res d Y').map (d.completedExchange sq K.obj) ≫
    (iotaT (g' := g') (f' := f') d K.obj K.property).hom

def constantComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :=
  (iotaS (f := f) (g := g) d K.obj K.property).hom ≫
    (S (f := f) (g := g) d ((res d X).obj K.obj)).hom ≫
    (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
      ((reduction d X).obj ((res d X).obj K.obj))) ≫
    (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv
```

## New

```lean
public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

def RhoNormalization (T : Scheme.{t})
    (e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T) : Prop :=
  ∀ P : CochainComplex (reductionModules T (d.completedRing T)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing T) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing T) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d T).map
              ((reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit d T
              (((reductionRestrict T (exchangeScalar d T)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeTowerRes d T).map (completedReductionTowerComplexCounit T d P) ≫
            (exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app
              ((completedReductionComplexTowerFunctor T d).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryRho d T).symm (.up ℤ)).hom.app P)

theorem rho_existsUnique (T : Scheme.{t}) :
    ∃! e : completedReductionTower T d ⋙ exchangeTowerRes d T ≅
        res d T ⋙ reduction d T,
      RhoNormalization d T e := by
  sorry

theorem rho_normalization (T : Scheme.{t}) : RhoNormalization d T (rho d T) :=
  (rho_existsUnique d T).exists.choose_spec

def LambdaNormalization (T : Scheme.{t})
    (e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T) : Prop :=
  ∀ P : CochainComplex (d.towers T) ℤ,
        (res d T).map (limitComplexUnit T (d.completedRing T) P) ≫
            e.hom.app (DerivedCategory.Q.obj P) ≫
            (rlim (A := A) T).map
              ((exchangeTowerModuleRes d T).mapDerivedCategoryFactors.hom.app P) =
          (reductionRestrict T (exchangeScalar d T)).mapDerivedCategoryFactors.hom.app
              (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryLambda d T) (.up ℤ)).hom.app P) ≫
            limitComplexUnit T (exchangeConstantRing T A)
              (((exchangeTowerModuleRes d T).mapHomologicalComplex (.up ℤ)).obj P)

theorem lambda_existsUnique (T : Scheme.{t}) :
    ∃! e : completedRlim T (d.completedRing T) ⋙ res d T ≅
        exchangeTowerRes d T ⋙ rlim (A := A) T,
      LambdaNormalization d T e := by
  sorry

theorem lambda_normalization (T : Scheme.{t}) : LambdaNormalization d T (lambda d T) :=
  (lambda_existsUnique d T).exists.choose_spec

def limitComplexUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T R) ℤ) :
    DerivedCategory.Q.obj
        (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (completedRlim T R).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((completedTowerLimit T R).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((completedTowerLimit T R).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (completedTowerLimit T R).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    (completedRlim T R).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

def rawComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (res d Y').map (d.completedExchange sq K.obj) ≫
    (iotaT (g' := g') (f' := f') d K.obj K.property).hom

def constantComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (iotaS (f := f) (g := g) d K.obj K.property).hom ≫
    (S (f := f) (g := g) d ((res d X).obj K.obj)).hom ≫
    (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
      ((reduction d X).obj ((res d X).obj K.obj))) ≫
    (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv
```

The `RhoNormalization` and `LambdaNormalization` bodies are exactly the original
predicates after the existential binder, without any mathematical edits. Consequently
unfolding either new predicate recovers the old theorem statement verbatim. The
projection lemmas use `.exists.choose_spec`, and the original choice bodies still use
`.exists.choose`. The explicit limit-unit and normalized-component types are their former inferred
types. Their bodies remain unchanged.

The exact local attribute commands are:

```lean
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  completedAdicChange reductionChange reductionDerivedChange reductionHomotopy
  completedReductionTower reduction

attribute [local instance 3000] orderedAbSheafify orderedAbLocallyBijective
  reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
  reductionRingModulesHasDerivedCategory

set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict completedReductionComplexTowerFunctor

attribute [local irreducible] ordinaryRho reductionModule completedReductionModuleTowerFunctor
  completedReductionCoefficient constantSheaf AdicCoefficients.coefficientRing
  SheafOfModules.monoidalCategory

attribute [local irreducible] RhoNormalization

attribute [local irreducible] ordinaryLambda Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit

attribute [local irreducible] limitComplexUnit

attribute [local irreducible] LambdaNormalization
```

The scoped `allowUnsafeReducibility` setting permits local normalization of the two
existing wrapper definitions. It changes elaboration and indexing, and does not disable
kernel checking; this is the same local-attribute pattern used elsewhere in the project.
The data and all exported reducibility statuses are unchanged. `ordinaryScalarDiagonal`
keeps the same identity components: its final naturality proof drops `rfl` after `simp`
already closes the goal under the local normalization setting.

All added private lemmas are proved. The local attribute commands in the delivered
module affect proof elaboration only; the exported categories and chosen localization
instances are the existing ones. No source-library file is edited.

## Users

Rechecked against the current source on 2026-10-22 with
`tools/downstream.py Sheaf.Paper.OrderedExchangeCoefficientComparison --uses
AlgebraicGeometry.Scheme.OrderedExchange.limitComplexUnit`:
only this item and `Sheaf.Paper.IntegralPullbackStrictRoosNormalization` mention the
changed `limitComplexUnit` signature. The required consumer row below is retained,
and its holder is refreshed from the current claim record. The tool `tools/downstream.py`
lists the following 18 downstream modules. The item is included separately.
No consumer source is changed. `IntegralPullbackStrictRoosNormalization.IsUnitNormalized`
uses `OrderedExchange.limitComplexUnit`: the added return type is its original inferred
morphism type, and the four-factor body is unchanged. Thus its normalization equation
retains the same mathematical meaning and needs no adaptation.
The consumers do not mention `rho_existsUnique`, `lambda_existsUnique`, `rawComponent`
or `constantComponent`; their uses of the existing comparisons retain the same data
and equations. Removed public imports are redundant through the remaining public imports.

The item and the unchanged consumers `CompletedExchangeCoherence` and
`IntegralPullbackStrictRoosNormalization` compiled against the sandbox outputs in 1.3, 8.3 and 41.0 seconds respectively,
without errors or warnings. The two unchanged consumers are excluded from delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | Three auxiliary proofs; named unchanged normalization predicates. |
| Sheaf.Paper.CompleteCompactSupportProetale | B7 | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.CompletedExchangeCoherence | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Uses limitComplexUnit in IsUnitNormalized; same morphism type and verbatim body; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.PulledReductionNormalizationComparison | E9 | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | M1 | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | J8 | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Existing signatures and comparison data retain their meaning; no adaptation. |

## Status

landed 20261021T203708-L-3854176 2026-10-21 (merge of deliver/K9/Sheaf.Paper.OrderedExchangeCoefficientComparison)

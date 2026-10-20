# AlgebraicGeometry.Etale normalized-support proof scopes

## Reason

The stage-3 visibility scan requests a change record for commands added to the existing
module. The new instance proofs are private lemmas registered with `[local instance]`
inside `namespace AlgebraicGeometry.Etale`, which ends in the same file. They are not
new global instances. A separate section makes three existing constructions locally
irreducible while checking the short-exactness proof, to avoid repeated expansion of
kernel and sheafification constructions. Its `end` restores the attributes before the
next public declaration. These are proof-scoped commands; no public signature,
definition body, public import, or target meaning changes.

## Old

The three private instance lemmas and their local registrations were absent. The
short-exactness proof had no local irreducibility section. The thirteen public theorem
proofs were `by sorry`. All original declaration signatures and non-theorem bodies are
preserved verbatim in the new source (apart from harmless whitespace in signatures).

## New

The three private, proved lemma signatures are:

```lean
private lemma supportι_mono (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (W : T.Opens) : Mono (supportedEtaleSectionsι A T W)

private lemma supportι_app_mono (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (W : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((supportedEtaleSectionsι A T W).app M)

private lemma openHom_subsingleton {T : Scheme.{u}} (U : T.Opens) (V : T.Etale) :
    Subsingleton (V ⟶ Scheme.Etale.mk U.ι)
```

Each is registered locally after its proof:

```lean
attribute [local instance] supportι_mono
attribute [local instance] supportι_app_mono
attribute [local instance] openHom_subsingleton
```

The short-exactness helper alone is enclosed by this local attribute scope:

```lean
section

attribute [local irreducible] supportedEtaleSections supportedEtaleSectionsι upperStar

-- The private, proved supportLocalizationSequence_shortExact theorem.

end
```

The three constructions retain their original definitions and original global
reducibility. No private helper appears in an existing public signature or public
definition body. Existing theorem proofs are completed, and the two additional general
results live in new Sheaf modules with their own DAG nodes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.NormalizedSupportTriangle --uses
supportedEtaleSections supportedEtaleSectionsι upperStar supportι_mono
supportι_app_mono openHom_subsingleton` was run. No existing source uses any of the three
new private names. The existing-name hits are covered by the table below, which also
includes all 58 transitive consumers, the item, and the two new modules. Holders are read
from the current claim records. Local attributes are restored before importers see the
module, so no consumer requires adaptation and no target-statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | G6 | Proofs completed; private helpers and local proof attributes added. |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | P7 | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Public statements and definitions retain their meaning; no adaptation. |
| `Sheaf.CategoryTheory.UnboundedInjectiveModel` | G6 | New proved theorem; no original consumer to adapt. |
| `Sheaf.CategoryTheory.UnboundedDerivedBoundary` | G6 | New proved theorem; no original consumer to adapt. |

## Status

landed 20261020T211723-L-3492915 2026-10-20 (merge of deliver/G6/Sheaf.AlgebraicGeometry.NormalizedSupportTriangle)

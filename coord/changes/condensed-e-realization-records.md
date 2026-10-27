# WeilConjectures.CondensedERealization shared declarations

## Reason

The mathematical proof is decomposed into the individual-operation realization system
and the separate ordered-square exchange comparison. Both statements must refer to the
existing records before their theorem modules can be imported by the target. Move those
unchanged records and the proved helper into a shared definitions module, reexported by
the original item. This resolves that import dependency without changing a record.

## Old

The original `Sheaf.Paper.CondensedERealization` declares the records and their helpers
in its own module, followed by the single existence theorem. Every public declaration
before `condensedE_realization` has exactly its source signature, body and attributes.

## New

```lean
public import Sheaf.Paper.CondensedERealizationDefinitions
import Sheaf.Paper.CondensedERealizationSystem
import Sheaf.Paper.CondensedERealizationSystemExchange
```

`CondensedERealizationDefinitions` retains the former item declarations and removes unused
private proof imports. All existing fully qualified declaration names and attributes
remain identical; the definitions have the same mathematical bodies and types. `moduleEncoding`, `fieldLowerStar`, `Along.rationalPull`, `Along.rationalPush`, and
`Data.pullOnOverHom` gain explicit definitionally equal return types. The latter is
`Rational l E U.scheme ⥤ Rational l E T.scheme`, equal to its inferred type.
The Data record specifies map endpoints explicitly.
The completed operation definitions are locally irreducible while checking the records;
this does not change their exported reducibility. The existence theorem's proof combines the
system and exchange statements. The target's mathematical meaning is unchanged; this
reorganization does not reopen its statement review for a changed definition.

## Users

The following cover all downstream modules and the server-reported textual users.
They continue to see the same declarations through the public reexport; no held module
is adapted. All downstream modules retain their original import path.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CondensedERealization | K9 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CondensedTateRealization | C9 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Z9 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CondensedERealizationDefinitions | new K9 module | Carries the unchanged declarations. |
| Sheaf.Paper.CondensedERealizationSystem | new K9 module | States individual-operation existence. |
| Sheaf.Paper.CondensedERealizationSystemExchange | new K9 module | States ordered exchange for a supplied system. |

| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | G6 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | K4 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | A8 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | A9 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | E4 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | T1 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.DlLocalHeartCoverDefects | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | G2 | Same public declarations through a public reexport; no source adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed | Server-reported user; same public reexport, no source adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Server-reported user; same public reexport, no source adaptation. |

## Status

landed 20261025T163831-L-860874 2026-10-25 (merge of deliver/K9/Sheaf.Paper.CondensedERealization)

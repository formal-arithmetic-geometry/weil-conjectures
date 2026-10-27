# AlgebraicGeometry.Scheme.Modules.etaleTensorSections_open_determination

## Reason

The proof now uses local generation, naturality, linearity and sheaf separatedness.
It does not use the separately selected section-normalized adjunction. Remove the
unused public import of TensorPullbackSectionAdjunction and the four unused private
proof imports. Every declaration signature and visibility is unchanged. No target
statement or definition changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.CategoryTheory.RingedSiteModules
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsLocalSpan
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
```

## Users

`tools/downstream.py` finds 42 downstream modules; its `--uses` search for the full
declaration name finds only the declaration itself. The two direct importers are
EtaleExtensionFreePresentationsHom and SchemeEtaleRelativeDifferentialsComparison.
Neither needs an adaptation. Both are compiled separately against this delivery.
The other downstream modules retain the interfaces of their direct dependencies.
No existing source-library module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineEtaleDerivedHomRealization | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AffineEtaleNaiveCotangentPresentation | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteFpModuleDirectImage | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentExtension | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleDetectsPerfect | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom | E5 | Direct importer; already imports TensorPullbackSectionAdjunction publicly. |
| Sheaf.AlgebraicGeometry.EtaleFiniteFreeZariskiDescent | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTypeModuleDetection | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtalePresentedModuleEffectiveRecovery | F5 | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FlatSpaceDerivedExternalCup | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.LogIdealAlgebraizationDescent | X2 | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSpaceDerivedBaseChange | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDegreeGMinusOneTheta | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SchemeDerivedEtaleQCohComparison | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SchemeEtaleRelativeDifferentialsComparison | F9 | Direct importer; retained dependencies provide every name used; checked separately. |
| Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceAffineNoetherianModuleApproximation | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceAffinePullPushExchange | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceClosedPushforwardRelativeFlatness | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceConnectiveNonnegativeFreeModel | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceEtaleIdealFactor | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceFlatRelativePseudoCoherence | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceInverseModulePerfectTestReduction | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceInverseModulePolynomialModel | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceNaiveCotangentFiniteLocalModel | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpacePerfectLimitCategory | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpacePerfectOpenRetract | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpacePerfectSourceHomContinuity | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceProjectiveSerreVanishing | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceProjectiveTwist | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceProperFlatH0Criterion | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpacePseudoCoherentTestsRelative | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceQuasiCoherentTorAmplitudeTest | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceRelativeFlatModulePushout | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceRelativePerfectFibreCriterion | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceSingleComplexBaseChange | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceSupportedApproximationSquareStep | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceSupportedKoszulHighLocalization | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpaceSupportedKoszulLowLocalization | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ZariskiEtalePseudoCoherentRHom | unclaimed | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare | N3 | Statement and declaration visibility unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorSectionsOpenDetermination | X3 | Own proof replaced; one unused public import and four private imports removed. |

## Status

landed 20261026T083508-L-2370724 2026-10-26 (merge of deliver/X3/Sheaf.AlgebraicGeometry.EtaleTensorSectionsOpenDetermination)

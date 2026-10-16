# CondensedFieldEvaluationFunctors redundant public import

## Reason

The second reading removed the redundant explicit public import
`Mathlib.Algebra.Category.ModuleCat.Basic`. Its public exports remain available
through the unchanged public chain
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` ->
`Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse` ->
`WeilConjectures.CategoryTheory.RingObjects.ContinuousMap` ->
`WeilConjectures.CategoryTheory.RingObjects.RingPresheaf` ->
`WeilConjectures.CategoryTheory.RingObjects.Ab` ->
`Mathlib.CategoryTheory.Preadditive.Yoneda.Basic` ->
`Mathlib.Algebra.Category.ModuleCat.Basic`.
The source of each public import in this chain was checked, and removing the
explicit Basic import compiles cleanly. The other added imports are proof-only.
No existing declaration signature, definition, instance, or target meaning changes.
The static delivery gate requires a change record even for a redundant public import.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Mathlib.Algebra.Category.ModuleCat.Basic
```

## New

```lean
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization

import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all Sheaf.Paper.InternalModuleAbEquivalence
```

## Users

`tools/downstream.py` lists the following 57 transitive importers. Holders are the
local claim snapshot at the second reading. The sole direct importer is
`Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars`. The public import
path above preserves every former public export, so every listed downstream
statement has exactly the same definitions, types, and instances available as
before. No consumer adaptation is required; no definition used by a target changed,
and no target statement review is reopened. This is import pruning only.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors` | C4 | Removed redundant import; public exports and existing declarations unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars` | B4 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | G1 | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.ContinuousLisseStratifiedLattices` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralConstructibleKernels` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralConstructibleSerre` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralReductionConservative` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralReductionConstructible` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `TargetsCheck` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No adaptation; all previous exports remain publicly reachable. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | No adaptation; all previous exports remain publicly reachable. |

## Status

landed 20261016T072553-L-972642 2026-10-16 (merge of deliver/C4/Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors)

# HomologicalComplex₂ bounded-below Cech cone imports

## Reason

Restore the module preserved at the quarantine path in coord/rework.tsv.
The archived file fails remote compilation because its public DoubleComplexTotal
import loads the old Sheaf filtration declarations alongside the upstream
CanonicalFiltration declarations. The concrete error names the duplicate
CategoryTheory.DecreasingFiltration.IsExhaustive. The module uses Mathlib total,
total.map and diagonal inclusions, but no declaration defined by DoubleComplexTotal.
Import those constructions directly and import integer intervals explicitly for
the finite supremum in cechTotalMapConeStep.

## Old

```lean
public import Sheaf.CategoryTheory.DoubleComplexTotal
```

## New

```lean
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Data.Int.Interval
```

All definitions, signatures, theorem bodies and docstrings are identical to the
quarantined source. In particular, the ordinary mapping cone, its degreewise
column tails, all spectral-sequence compatibility conditions and the arbitrary
integer lower bound are preserved. The original one theorem hole is retained.
The existing DAG attachment, mathematical dependencies and proof plan are
unchanged. No target statement or definition used by a target is changed.

## Users

The source-only downstream tool reports unknown module because this item is
quarantined. An exhaustive import and declaration-name search of lean/ and
quarantine/ finds no live importer and the following two archived direct
importers. Neither refers to a declaration of this module in its current proof;
both retain the import as the dependency of an unfinished parent proof.
The imports are private proof imports, so the removed public re-export supplies
no names to their public statements. No consumer adaptation is needed.
The DAG also retains both parent dependency edges and their unit route.
No archived file is deleted or modified.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.BoundedBelowCechConeComparison | Q1 | Restore the quarantined module with direct imports; remote compile succeeds. |
| Sheaf.TraceFormula.FiniteBaseCechHypercohomology | unclaimed, quarantined | Proof import retained; no declaration, signature or definition changes. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed, quarantined | Proof import retained; no declaration, signature or definition changes. |

## Status

landed 20261020T162319-L-3589035 2026-10-20 (merge of deliver/Q1/Sheaf.CategoryTheory.BoundedBelowCechConeComparison)

Remote compilation reproduces the archived duplicate-declaration error (0.5 s).
The repaired source compiles successfully (1.7 s). Removing the broad import
first exposed the missing LocallyFiniteOrder integer instance; the explicit
Mathlib.Data.Int.Interval import supplies it. Full consumer restoration is outside
this packet; those consumers remain quarantined for their own assigned repairs.

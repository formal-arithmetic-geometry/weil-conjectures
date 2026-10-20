# CategoryTheory.secondFiltration_two_column_image

## Reason

Restore the quarantined module assigned in coord/rework.tsv. Compiling the archived
module reproduces the import failure: the environment already contains
CategoryTheory.DecreasingFiltration.IsExhaustive from Sheaf.CategoryTheory.Filtration
when WeilConjectures.CategoryTheory.CanonicalFiltration loads. The adopted row-comparison
proof dependencies use WeilConjectures.CategoryTheory.DoubleComplexTotal. Import that
same provider publicly instead of the duplicate Sheaf provider. The repaired complete
module compiles in 9.2 seconds without warnings.

## Old

```lean
public import Sheaf.CategoryTheory.DoubleComplexTotal
```

## New

```lean
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
```

Every declaration, including all proof bodies, is restored verbatim from the quarantine
archive; this is the only Lean edit. The finite diagonal image-sum formula in hL and
the theorem's hypotheses and conclusion are preserved. No construction or target
statement is edited. The existing node attachment and proof dependencies are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SecondFiltrationTwoColumnImage | S1 | restored and import repaired |
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence | quarantined; no adaptation | its existing call at line 970 retains the same theorem interface |

There are no active Lean consumers in lean/; the quarantined consumer is preserved.
It imports this module with import all and calls the unchanged theorem. Its own rework
is independent of this import repair; no consumer file is edited here.

## Status

landed 20261020T162550-L-3625757 2026-10-20 (merge of deliver/S1/Sheaf.CategoryTheory.SecondFiltrationTwoColumnImage)

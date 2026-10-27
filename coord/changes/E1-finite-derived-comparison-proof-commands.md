# CategoryTheory.FiniteDerivedComparison proof controls

## Reason

The composition proof repeatedly uses the total tensor structure. A local priority for its
structure instance and proved component interfaces avoid expanding the full monoidal structure. No target statement, public signature,
public import or public definition body changes.

## Old

The original module uses its existing irreducibility commands without a private sheaf-composition
cache or local monoidal-instance priorities.

## New

The existing `HomologicalComplex.monoidalCategoryStruct` receives local priority 100000. The chosen tensor comparison is kept locally irreducible, and private
proved component equations are used when rewriting resolving squares. `Elab.async` is false.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteDerivedComparisonNormalization | E1 | Composition proof; public contracts unchanged. |

## Status

landed 20261025T204517-L-2965299 2026-10-25 (merge of deliver/E1/Sheaf.Paper.FiniteDerivedComparisonNormalization)

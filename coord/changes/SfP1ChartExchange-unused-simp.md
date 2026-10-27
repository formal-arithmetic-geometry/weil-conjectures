# SfP1ChartExchange proof cleanup

## Reason

The item delivery's local preflight compiles the unpublished dependency
`Sheaf.AlgebraicGeometry.SfP1ChartExchange`; its existing proof emitted three
unused simp argument warnings. Remove only those unused arguments so the required
single-file probe is warning-free.

## Old

The final `simp only` call in `LineComparisons` listed
`ordinaryFinitePullback`, `ordinaryFiniteLine`, and `ordinaryFiniteDegreeZero`.

## New

The same proof and theorem signature remain, with those three unused simp
arguments removed from the final `simp only` list.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RationalProjectionTensorCompatibility | R2 | Direct unpublished dependency; the adapted proof compiles without warnings. |

## Status

landed 20261026T235930-L-1471377 2026-10-26 (merge of deliver/R2/Sheaf.Paper.RationalProjectionTensorCompatibility)

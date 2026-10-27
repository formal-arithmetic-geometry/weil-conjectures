# RepresentativeComparison predicate factorization

## Reason

Withdrawn by the reviewer (2026-10-26, delivery head `9c075bb5acfe`). The delivery proposed
factoring the subtype predicate of `RepresentativeComparison` in
`Sheaf.Algebra.Homology.FiniteFreeCompletionExchange` through a new generic
`representativeComparisonCondition`. The change is not forced: the published module compiles
against the delivered dependencies, and the item compiles against the published module
(reviewer compile 52.9 s, the published module itself 34.9 s against 46.6 s for the
factored version). An unforced body change of a definition held by no group is not made.
The module stays at its published version.

## Old

The published `def RepresentativeComparison` subtype.

## New

Unchanged (no change is made).

## Users

None affected: the declaration is unchanged.

## Status

withdrawn

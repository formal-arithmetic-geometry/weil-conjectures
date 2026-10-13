# AlgebraicGeometry.tensorHomUncurry_normalized_comparison

## Reason

The assigned module and node existed in the worker's initial checkout, but the latest fetched delivery base lacks both. Restore the assigned statement and its compiling reduction, without changing the original signature or meaning. This is not an intentional change to any target or existing definition.

## Old

Absent on the fetched base; the originally assigned theorem had the same signature with proof `by sorry`.

## New

The assigned theorem has its unchanged original signature and the factorization proof in the delivered module. Its two intermediate dependencies are explicit new nodes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | unclaimed | Original expected comparison declaration restored unchanged |

## Status

landed 20261013T095950-L-2457790 2026-10-13 (merge of deliver/F2/Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison)

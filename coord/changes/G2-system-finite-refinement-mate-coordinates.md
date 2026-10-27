# Sheaf.Paper.SystemFiniteRefinementMateCoordinates

## Reason

The rework item had one open target theorem and a stale global-build record
reporting missing `Sheaf` imports. The restored source compiles with the current
imports. The target proof now exposes the canonical bridge evaluation and the two
independent finite-coordinate transport steps as explicit declarations. The left
transport is closed by bridge naturality and iso cancellation.

## Old

`refinementMate` was proved by `sorry`; no intermediate modules existed for the
canonical bridge evaluation or for the two coordinate normalizations.

## New

`refinementMate` is proved by transitivity through
`canonicalEvaluation`, `lhsNormalization`, and `rhsNormalization`. The first
intermediate is proved; the latter two are named split-off statements whose
conclusions respectively normalize the left and right sides of the target.
The direct importer `Sheaf.Paper.SystemRefinementFiniteCoordinates` keeps its
signature and compiles unchanged against the delivery.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SystemRefinementFiniteCoordinates | D5 | Existing private proof uses `refinementMate`; its source compiles unchanged. |
| Sheaf.Paper.SystemFiniteRefinementMateCanonical | G2 | New intermediate module imported by the item. |
| Sheaf.Paper.SystemFiniteRefinementMateLhsNormalization | G2 | New split-off left transport statement. |
| Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization | G2 | New split-off right transport statement. |

No existing declaration signature or mathematical definition was changed.

## Status

landed 20261027T210003-L-1641988 2026-10-27 (merge of deliver/G2/Sheaf.Paper.SystemFiniteRefinementMateCoordinates)

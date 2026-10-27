# Sheaf.Paper.ExceptionalSiteOriginComparison

## Reason

The item proof needs the site-comparison construction, finite inverse lower-bound
transport, and evaluation lower-bound transport as separate interfaces. The delivery
therefore adds one private proof module with three named theorem obligations and
assembles the original item theorem from them.

## Old

`Sheaf.Paper.ExceptionalSiteOriginComparison` contained the unchanged target
statement with one proof hole and imported only
`Sheaf.Paper.ExceptionalSystemInterfaces`.

## New

The target statement and all existing declarations remain unchanged. The item adds a
private import of `Sheaf.Paper.ExceptionalSiteOriginComparisonCore`. That module adds
three public theorem interfaces, each strictly smaller than the target: evaluation
preserves `IsGE`, the finite inverse preserves `IsGE`, and the core comparison
construction supplies the equivalence and levelwise assertions. Their proofs remain
named stage-3 obligations; the item proof combines them by a real origin-witness and
isomorphism argument.

## Users

| Module | Group | Effect |
| --- | --- | --- |
| `Sheaf.Paper.ExceptionalSiteOriginComparison` | V5 | Uses the new private proof interfaces. |
| `Sheaf.Paper.ExceptionalSystemTransport` | unclaimed | Existing importer compiled unchanged against the delivery. |
| `Sheaf.SixFunctors.ExceptionalIntegralSystemExistence` | unclaimed | Existing importer compiled unchanged against the delivery. |

## Status

landed 20261027T180927-L-3913880 2026-10-27 (merge of deliver/V5/Sheaf.Paper.ExceptionalSiteOriginComparison)

## Reason

The assigned affine restriction proof needs the global closed-chart/affine-space
factorization as a named intermediate step.

## Old

No named factorization theorem was available to the assigned module.

## New

`AffineRestrictionMapIso.lean` adds
`finiteDualizing_etaleComparison_factorization` with one split proof hole.

## Users

`Sheaf.SixFunctors.FiniteDualizingAffineRestriction` imports the helper and transports
its two invertible factors through the affine derived inverse-image functor.

## Status

Added as a stage-3 split node; downstream users compile successfully.

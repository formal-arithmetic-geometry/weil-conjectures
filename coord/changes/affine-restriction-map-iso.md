## Reason

The assigned affine restriction proof needs the global closed-chart/affine-space
factorization as a named intermediate step. Its proof reduces to the strictly
simpler global invertibility statement, which is recorded as a separate node.

## Old

No named factorization theorem was available to the assigned module.

## New

`AffineRestrictionMapIso.lean` adds
`finiteDualizing_etaleComparison_factorization` and proves it from
`finiteDualizing_etaleComparison_isIso_for_factorization`. The latter is the
single split proof hole in the delivery.

## Users

`Sheaf.SixFunctors.FiniteDualizingAffineRestriction` imports the helper and transports
its two invertible factors through the affine derived inverse-image functor. The
new auxiliary module is imported only by the helper.

## Status

Added as a stage-3 split node; downstream users compile successfully.

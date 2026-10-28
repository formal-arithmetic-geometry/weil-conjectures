# scalarAtClosure interface relocation

## Reason
The universe-reindexed scalar construction is moved into its own data module so the
certificate theorem can use an opaque normalization-transport theorem without unfolding
large derived-category inclusion definitions during elaboration. The construction itself
is unchanged.

## Old
`WeilConjectures.ConstructibleExceptionalCoefficients.scalarAtClosure` and its helper
fields `scalarFunctorAtClosure`, `scalarRealizationAtClosure`, `scalarCommShiftAtClosure`,
`scalarAdditiveAtClosure`, and `scalarExactAtClosure` were declared in
`Sheaf.Paper.RingEndpointScalarIdentityTransfer`.

## New
`scalarAtClosure` is declared in
`Sheaf.Paper.RingEndpointScalarIdentityTransferData`, with the helper fields inlined by
the explicit finite/integral case splits. The assigned theorem module imports this data
module and the normalization transport module.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.RingEndpointScalarRestrictions` | unclaimed | Its existing uses of `scalarAtClosure` continue through the new public data module. |
| `Sheaf.Paper.RingEndpointScalarIdentityTransfer` | Y3 | Imports the data module and uses the moved definition. |

## Status
landed 20261028T020920-L-2564273 2026-10-28 (merge of deliver/Y3/Sheaf.Paper.RingEndpointScalarIdentityTransfer)

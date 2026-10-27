# AlgebraicGeometry.Etale.sfEtaleGraphTensorMap

## Reason

Expose the actual morphism needed to state the graph-transfer and exchange/projection
parts of the existing graph-unit proof. This is a new composite, with no choice and no
postponed proof in its construction. Existing signatures and public imports are unchanged.

## Old

No declaration named AlgebraicGeometry.Etale.sfEtaleGraphTensorMap.

## New

AlgebraicGeometry.Etale.sfEtaleGraphTensorMap A e c M K, in
Sheaf.AlgebraicGeometry.SfEtaleGraphTransferTensor, is the map
Ls*(Dj_! M) tensor Lq*(D(e*) K) to Ls*(Dj_!(M tensor D(e*) K)).
It is the tensor of identity with Lq* of the inverse exact/left-derived comparison,
then the inverse-image square comparison, inverse tensor comparison for s, and
Ls* of the inverse open projection followed by Dj_! of the tensor of identity with
the compactification composition comparison and the exact/left-derived comparison.
The complete Lean signature and body are in the new module of this delivery.

No existing definition or theorem statement changes, so target meanings are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfEtaleGraphTransferTensor | B4, new | Explicit map used in the new transfer equation. |
| Sheaf.AlgebraicGeometry.SfEtaleGraphExchangeTensor | B4, new | Same composite used in the exchange equation. |
| Sheaf.AlgebraicGeometry.SfEtaleGraphUnitTensor | B4 | Proof uses the two equations at this map. |

The name is new; there are no pre-existing users. No consumer needs adaptation.

## Status

landed 20261025T161957-L-175460 2026-10-25 (merge of deliver/B4/Sheaf.AlgebraicGeometry.SfEtaleGraphUnitTensor)

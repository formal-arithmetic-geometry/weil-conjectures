# CategoryTheory.MonoidalClosed.biduality_of_bounded_heart

## Reason

Separate the geometric sheaf case from the formal bounded-truncation proof of
canonical Verdier biduality. New public declarations live in Sheaf modules.
No existing definition or statement changes.

## Old

There was no `biduality_of_bounded_heart` or
`isIso_biduality_constructible_sheaf` interface. The item contained the single
hole `AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality`.
Its signature, all other source declarations and all public imports are unchanged.

## New

`Sheaf.PoincareDuality.BidualityTruncation` proves biduality on bounded objects
from biduality on their heart objects. Its statement allows any derived
object W and any isomorphism-invariant property Q of heart objects.

`Sheaf.PoincareDuality.ConstructibleSheafBiduality` states the geometric input
for constructible module sheaves in degree zero and a structure morphism whose
target is isomorphic to Spec k. This is the packet's sole remaining hole.

The original item assembles these two results by reflecting the ambient
isomorphism into the full bounded-constructible subcategory. No target meaning
changes and no consumer adaptation is required.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Verdier | S6 | Private proof imports of both new interfaces; unchanged public signatures. |
| Sheaf.PoincareDuality.BidualityTruncation | S6 (new) | Fully proved formal interface. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | S6 (new) | Separate geometric sheaf statement with one hole. |

The new modules had no previous consumers. No existing interface changes, so
there are no forced adaptations or downstream meaning changes to audit.

## Status

landed 20261025T013242-L-3945229 2026-10-25 (merge of deliver/S6/WeilConjectures.PoincareDuality.Verdier)

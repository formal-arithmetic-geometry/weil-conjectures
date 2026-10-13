# singletonTensor_normalized_restriction proof scopes

## Reason

Preflight conservatively classifies newly added option and attribute commands as
an interface change. These commands affect elaboration inside this module only.
All attributes explicitly carry `local`, every new helper is private, and the
existing theorem signature is textually identical. The change replaces its proof
and adds a proof-only import; no public definition, notation, instance, or
statement changes. The equality-witness wrapper is private and fully proved.

## Old

Before the theorem, the original module has no local proof options or attributes.
Its public signature is exactly the one retained in the delivered module.

## New

The module locally sets `backward.isDefEq.respectTransparency` and its `types` option to true and marks tensor pullback and restrictions locally irreducible. These commands export no changes.

## Users

`tools/downstream.py --uses singletonTensor_normalized_restriction` reports 171
indirect dependent modules and the following two textual users. None needs an
adaptation, because all public signatures and visibility remain identical and the
new reducibility attributes are local.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction | B2 | Its proof is completed; signature unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface | unclaimed in this clone's claims | Its existing application has the identical signature; no edit. |

## Status

landed 20261013T160708-L-1370637 2026-10-13 (merge of deliver/B2/Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction)

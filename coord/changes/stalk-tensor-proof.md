# Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor proof visibility

## Reason
The proof adds local helper declarations and imports a presheaf comparison module. The stage-3 checker reports that the module's command environment changes what importers see, so this record documents the proof-side interface change.

## Old
The module contained only its public imports, namespace commands, and the sorry theorem.

## New
The module contains the same public theorem statement and public imports, plus private helper declarations and proof-only imports needed to construct and verify the stalk tensor comparison.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor importers | unclaimed | Public theorem signature is unchanged; proof-only helpers are private. |
| Sheaf.Topology.PresheafStalkTensor importers | Q2 | New presheaf theorem is available for the item proof. |

## Status
landed 20261012T173854-L-3303066 2026-10-12 (merge of deliver/Q2/Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor)

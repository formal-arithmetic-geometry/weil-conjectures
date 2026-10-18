# Proof imports and local instances

## Reason
The proof needs local sheaf and abelian instances and imports the two new lower modules.

## Old
No proof-only imports.

## New
Proof-only imports of the extension presentation obligations and local instance attributes.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension | K5 | required proof context |

## Status
landed 20261018T071201-L-1671186 2026-10-18 (merge of deliver/K5/Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension)

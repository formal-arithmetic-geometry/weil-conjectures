# IntegralExtensionByZero proof scope

## Reason

The completed proof adds private proof helpers and proof-only imports. The
delivery checker classifies the local universe/open/attribute commands needed by
the proof as changes to the module's visible environment, so this record
documents that required proof scope explicitly.

## Old

The item module contained the unchanged public theorem signature with a `sorry`
proof and imported the original proof-dependency modules.

## New

The theorem keeps the same signature and public imports. Its proof uses private
helpers, local universe declarations, local namespace openings, and local
irreducibility attributes, together with the two new helper theorem modules.
No public definition or theorem signature is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralExtensionByZero | A3 | Proof and proof-only imports; public theorem signature unchanged. |
| Sheaf.Paper.CondensedOpenExtensionProducts | A3 | New helper theorem required by the item proof. |
| Sheaf.Paper.IntegralOpenExtensionReduction | A3 | New helper theorem required by the item proof. |

## Status

landed 20261019T002455-L-2138478 2026-10-19 (merge of deliver/A3/Sheaf.Paper.IntegralExtensionByZero)

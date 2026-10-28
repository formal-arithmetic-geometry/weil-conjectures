# normalized_reindexing_identity decomposition

## Reason

The proof is decomposed into a finite-stage cancellation theorem and a directed-stage
assembly theorem. The item gains proof-only imports of these new modules.

## Old

`normalized_reindexing_identity` was a theorem with a single proof hole in
`Sheaf.Paper.AdicReindexingIdentity`.

## New

`normalized_reindexing_identity` obtains
`NormalizedReindexingFiniteCertificate` from
`normalized_reindexing_identity_finite` and applies
`normalized_reindexing_identity_from_finite`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicReindexingFunctoriality | D2 | proof imports the item; its interface is unchanged |

## Status

landed 20261028T020557-L-2525939 2026-10-28 (merge of deliver/M3/Sheaf.Paper.AdicReindexingIdentity)

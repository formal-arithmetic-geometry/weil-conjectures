# Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull
## Reason
The delivery adds proof-only helper modules and imports them in the parent proof.
## Old
The parent module imported only `Sheaf.ConstructibleSheaf.TorsorAssociatedModule`.
## New
The parent module imports the three helper theorem modules needed by its proof.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull | N1 | proof imports three helper declarations |
## Status
landed 20261012T135257-L-1679505 2026-10-12 (merge of deliver/N1/Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull)

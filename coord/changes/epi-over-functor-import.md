# epi-over-functor-import
## Reason
The item proof imports the new intermediate theorem `epi_overFunctor_map`.
This proof-only import is required to provide the restricted epimorphism instance.
## Old
The item had no import of `Sheaf.AlgebraicGeometry.EpiOverFunctor`.
## New
The item imports `Sheaf.AlgebraicGeometry.EpiOverFunctor` privately.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteTypeEpiImage | B4 | uses the restricted epi theorem |
## Status
landed 20261013T010611-L-2669366 2026-10-13 (merge of deliver/B4/Sheaf.AlgebraicGeometry.FiniteTypeEpiImage)

# cartesianHigherImage_stalk_colimit
## Reason
The original module exposed an unproved stalk-colimit route that the delivered germ proof does not use. Removing it prunes an unneeded declaration and avoids retaining a second equivalent geometric split.
## Old
The declaration `AlgebraicGeometry.Etale.cartesianHigherImage_stalk_colimit` in `CartesianHigherImageGermVanishing.lean`.
## New
The declaration is removed; the module exports only the assigned germ-vanishing theorem.
## Users
| module | group holding it | effect |
|---|---|---|
| none found | unclaimed | no adaptation required |
## Status
landed 20261014T202735-L-2258468 2026-10-14 (merge of deliver/R1/Sheaf.AlgebraicGeometry.CartesianHigherImageGermVanishing)

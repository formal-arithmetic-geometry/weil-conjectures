# AlgebraicGeometry.ProEtale.VaryingRing.tensorComparison_exists

## Reason

Fill the existing proof while retaining its exact public statement and import.
The new sections, opens and local irreducibility attributes are proof contexts.
The normalized linear adjunction, its tensor comparison, and the total-complex
comparison need equations that the existing existential wrappers do not retain.
Private proved helpers record these equations without changing the public API.

## Old

The sole public theorem `tensorComparison_exists`, with the original header in
`lean/Sheaf/AlgebraicGeometry/VaryingRingTensorComparison.lean`, has body `by sorry`.
The only public import is `Sheaf.AlgebraicGeometry.VaryingRingOperations`.

## New

The theorem header and public import remain verbatim. Proof-only imports expose
the already constructed algebraic inverse image, scalar extension, ordinary
tensorator, K-flat preservation, and representative descent. Every added
declaration is private. `transportedOrdinary` is an actual composite of three
specified isomorphisms; its naturality and cancellation equations are proved.
The local irreducibility attributes prevent repeated unfolding of the module
monoidal construction. There are no changes to existing public definitions,
instances, signatures, attributes, or data. There are no source-library edits.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.VaryingRingTensorComparison | G4 | Existing theorem proof; private helpers only. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Its direct use of the theorem has the identical signature and public imports. |

`tools/downstream.py --uses` reports only the item and `SystemTensorMateArrows`
as declaration-name users. The other direct importers,
`Sheaf.Paper.TowerOperationsGroundFieldRetagging` and
`Sheaf.Paper.ProjectionReductionPresentation`, likewise see the original API.
All 26 transitive importers receive the unchanged public interface. No consumer
file is modified or requires adaptation.

## Status

landed 20261025T014627-L-21164 2026-10-25 (merge of deliver/G4/Sheaf.AlgebraicGeometry.VaryingRingTensorComparison)

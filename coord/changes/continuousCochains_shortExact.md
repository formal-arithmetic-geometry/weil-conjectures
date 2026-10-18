# Rep.continuousCochains_shortExact

## Reason

The delivered proof changes the public theorem interface fingerprint according to the stage-3
checker because the theorem is wrapped in a local `set_option maxHeartbeats 800000 in` command
needed to elaborate the dependent topology instances and degreewise exactness within the file
limit. The theorem's binders, universes, hypotheses, and conclusion are unchanged verbatim.
The delivery also changes the item's proof dependency route to use the already proved coordinate
module and adds only proof-only imports.

## Old

The original declaration is the theorem `Rep.continuousCochains_shortExact` in
`lean/Sheaf/RepresentationTheory/ContinuousCochainsShortExact.lean`, with the exact signature
recorded in the item's DAG `lean.statement`; its body was `by sorry`.

## New

The exact same declaration signature, now proved by explicit continuous-map complexes,
pointwise exactness, and `HomologicalComplex.shortExact_of_degreewise_shortExact`. The local
heartbeat option affects elaboration only; it does not alter the theorem type.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RepresentationTheory.ContinuousCochainsDeltaFunctor | unclaimed | imports the theorem; signature unchanged |
| Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants | unclaimed | transitive importer; no source change required |
| Sheaf.RepresentationTheory.DiscreteContinuousCohomology | unclaimed | transitive importer; no source change required |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | transitive importer; no source change required |

## Status

landed 20261018T062834-L-664299 2026-10-18 (merge of deliver/M4/Sheaf.RepresentationTheory.ContinuousCochainsShortExact)

# Delivery report: lemma-weil-pbc-fibre-product-limit

## Files written

- dag/nodes/sec-curve-estimates/lemma-weil-pbc-fibre-product-limit.json: repaired split; no new nodes or Mathlib leaves.

## Attachments

None. The source checkout has no declaration tagged with this node or stating its exact neighbourhood-limit claim.

## WANTED

None. The source paths under `literature/` are not materialized on this machine; I used the item's imported blueprint sketch, the cited DAG statements, and the public Stacks pages for Tags 01YW, 0BUC, 04E7, and 03PQ.

## Problems found and repaired

The prior step 2 treated the directed reindexing as cofinal in the original neighbourhood category, although its cited statement only supplies a limit over a directed set. I removed the directed-system reduction and the scheme-over-limit tool use. The new proof first extends the strict-henselization limit from affine representatives to all pointed neighbourhoods, then proves the fibre-product cone limiting by its universal property. There is no stage-0 notation, so the two meanings of S_0 are gone. I also added the strict-henselization and fibre-product definitions to the statement dependencies and every cited proof node to proof_deps.

## What remains unfinished

Nothing for this stage-1 split.

## Review by H1

I checked the item's imported blueprint proof sketch: it claims the fibre-product limit by affine tensor-colimit comparisons and chart gluing. I checked the Stacks source statements for Tag 01YW (an affine inverse limit as the spectrum of the ring colimit), Tags 0BUC and 04E7 (cofinal full subcategories and colimit comparison), and Tag 03PQ (common refinements in the pointed etale neighbourhood category). The generic claim in the item follows more directly from the universal properties; the blueprint's quasi-compact and quasi-separated hypotheses remain in the statement but are not needed in this proof. The source file itself is absent from this machine's literature checkout, so the imported sketch is the available local copy of that proof.

For step 1, I read [def-weil-pbc-strict-henselization-limit] for the small full category J of affine representatives and the colimit ring, and [lem-weil-pbc-spec-small-colimit-limit] for the limit cone over J. Each affine object is isomorphic to a representative by the definition's stated choice of J. Transporting projections through those isomorphisms extends the cone and its universal property to every affine pointed neighbourhood; clause (2) of [lem-weil-pbc-colimit-initial-full-subcategory] identifies the two limits once both exist. [lemma-weil-pbc-affine-neighbourhood-cofinal] states exactly that the affine full subcategory is initial in all pointed neighbourhoods, and clause (1) of the same colimit node transfers the limit to the full category after passage to opposite categories. [lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered] supplies nonemptiness and says (S,sbar) is an object; the projection at S is the structure map. I checked that clause (2) requires existence on both sides, and corrected the step to construct the affine limit before applying it.

For step 2, [def-pc-fibre-product] supplies both projections and uniqueness from a compatible pair. The V-components of a cone to X times_S V give a map into the limit from step 1. [lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered] supplies a common refinement U for any V and W, so compatibility forces their X-components to agree. At the object S, the fibre-product condition gives equality of the maps T to S needed to pair the common X-map with the strict-henselization map. The two projection uniqueness statements prove existence and uniqueness of the resulting map into X times_S S_(sbar). I checked the single-object case: when the diagram contains only S, the argument reduces to X times_S S is X. No new statement is introduced, and no directed-system converse or finite-cover assertion remains.

I checked B through E against the node: it contains no new unsplit child or Mathlib leaf (B); each non-elementary transfer and the fibre-product definition is cited in the step that uses it, with proof_deps their union (C); the steps construct the item's universal map rather than restating its conclusion in a child (D); all limits use the same neighbourhood diagram, the common-refinement arrows have the correct direction, and no affine-cover or quasi-separated intersection hypothesis is silently used (E). The earlier return's notation collision, unsupported cofinality assertion, and stale tool use have been removed.

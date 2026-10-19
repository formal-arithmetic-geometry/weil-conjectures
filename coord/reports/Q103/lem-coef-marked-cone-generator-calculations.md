## Files written

- `dag/nodes/sec-six-functors/lem-coef-marked-cone-generator-calculations.json`: repaired the returned item; retained its statement, Lean record, route, and old steps, and replaced the 2635-character step 8 by six short steps (steps 8–12 plus the unchanged terminal calculation as step 13).
- `dag/nodes/sec-six-functors/lem-coef-cone-triangle-mapping-square.json`: new unsplit statement node for the coherent cone square induced by a triangle.
- `dag/nodes/sec-six-functors/lem-coef-marked-action-edge-comparison.json`: new unsplit statement node for passing from vertex actions to arbitrary acting edges.
- `citations.json`: 40 verbatim node-statement quotations, one for every item-step citation.

There are two new unsplit nodes and no Mathlib leaves. The item is now `split`.

## Attachments

No attachment. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its title, and the marked-cone terminology. The source contains no declaration carrying this item and no sorry-free declaration with the item's full statement. The retained Lean record is a later stage-2 record with a different formal statement and does not close this stage-1 node.

## WANTED

WANTED: J. Lurie, *Higher Topos Theory* (HTT.pdf), Propositions 3.2.1.11 and 3.2.1.14 and the surrounding Section 3.2.1 calculations, for the item and both new nodes. The PDF was read online on 2026-10-17 but is not archived under `literature/`. The proof therefore keeps `proof_origin.by = agent` and cites the online source places.

## Problems corrected or reported

The return identified only one defect: item proof step 8 was 2635 characters and hid several lemmas. I did not alter the item's statement, Lean record, source route, or the other proof steps. I separated step 8 into: the two Kan horn fillings; the coherent cone square and its marked-side consequences; the categorical inverse calculation; the vertex-to-edge action comparison; and the projective trivial-cofibration conclusion. Every non-elementary replacement step is below 2000 characters.

The two hidden comparisons are strict subclaims used by the fourth marked-anodyne generator and are smaller than the item. I searched the complete DAG and blueprint for each before creating it. No existing node states either comparison. The Mathlib searches returned only ordinary horn pushouts, edge composition, homotopy-category edge classes, and unrelated ordinary cones; after reading those declarations, neither comparison qualified as a Mathlib leaf. The search commands and their outputs remain in `searches.jsonl`.

## Not duplicates

`lem-coef-cone-triangle-mapping-square` vs existing cone/square nodes: the new statement concerns the specific coherent realization cone $P=\mathfrak C[K\star\Delta^0]$, its coning edges, and the square attached to a 2-simplex; existing cone-square nodes concern unrelated ordinary, dg, or abstract coherent squares and do not state this construction.

`lem-coef-marked-action-edge-comparison` vs existing action/marked nodes: the new statement compares a marked simplicial action at a vertex with the action of an arbitrary parameter edge and tests equivalences in a quasicategory; existing marked nodes define marked model structures or cone markings and do not state this vertex-to-edge equivalence criterion.

## Review by Q103

I read the current repository item, its `blueprint.from` ancestor `prop-coef-integral-exceptional-adjoint`, the `sk-prop-sf-biduality-general` unit and chapter, the retained search log, and the full HTT source passages for Definition 3.2.1.2, Lemmas 3.2.1.8–3.2.1.10, Proposition 3.2.1.11 (especially case (4)), and Proposition 3.2.1.14. I also read every cited DAG statement used by all thirteen item steps. The item statement and hypotheses are unchanged; the new nodes introduce their own simplicial sets, coherent cone, markings, actions, and quasicategory test maps.

Steps 1–7 retain the existing construction, cube boundary, pure marking, inner-horn, final-horn, detector, and square-generator arguments. For each, I opened every cited statement and checked that it supplies exactly the construction or model-category property named in the step. In repaired steps 8–12, the horn statement supplies the two inverse witnesses; `lem-coef-cone-triangle-mapping-square` supplies the square and its four sides; `lem-coef-infinity-mapping-composition` supplies composition in the homotopy category and the equivalence-edge criterion; `lem-coef-marked-action-edge-comparison` supplies the passage from constant vertex actions to arbitrary acting edges; and the marked-model and projective-calculus nodes supply the weak-equivalence and cofibration conclusions. Step 10 is elementary inverse algebra from the displayed equations. Step 13 is the retained terminal $Q^n$ coend calculation and cites the pinched-cube statement.

I checked the hypotheses in the new nodes on the edge cases used by the item: degenerate triangles, identity edges, an empty Kan complex, empty indexing/evaluation, arbitrary acting edges, and the absence of any Kan assumption on coherent mapping simplicial sets. The action comparison does not assume the acting parameter is Kan; it uses only the stated marked square and its equivalence side edges. The cone-square statement is natural under precomposition, so it applies to every vertex evaluation. No SGA source is cited, no coefficient category is changed, and no statement is weakened.

For the new nodes I read their HTT source places, searched the entire DAG and blueprint, ran LeanFinder/LeanSearch/Loogle/Mathlib-grep queries recorded in `searches.jsonl`, and read the returned Mathlib files. Both nodes are statement-only as required. The item’s `proof_deps` is the union of its step uses, and `citations.json` was checked mechanically: every quote is a verbatim substring of its cited node statement. The repair addresses the returned long-step point and leaves no non-elementary item proof step at or above 2000 characters.

## Unfinished work

No stage-1 split work remains. The required server dry run is the next operation; no compiler, Lake, or local DAG/review script is run on this machine.

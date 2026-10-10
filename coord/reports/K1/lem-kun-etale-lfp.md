# Stage 1 report: lem-kun-etale-lfp

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-etale-lfp.json`: item, split with one elementary proof step; no new nodes.
- `citations.json`: two verbatim quotes for the conventions dependency.

## Attachments

None. A search for `lem-kun-etale-lfp`, étale, and locally finite presentation in both project source checkouts found no sorry-free declaration stating the item.

## WANTED

None.

## What was checked

The imported item was checked against its blueprint proof paragraph. The existing `def-weil-pbc-scheme-conventions` node was read in full; it explicitly defines étale to include locally finite presentation and identifies finite type with quasi-compact plus locally finite type. The item has no additional statement dependencies. The proof step spells out the remaining elementary composition argument: the composite `U -> X -> Spec K` is quasi-compact and locally of finite type, so it is finite type. The step is marked elementary because these are direct closure checks from the cited definitions.

Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch (the latter was unavailable), with a second phrasing for LeanFinder, Loogle, and grep. The hits provided only general ring-level étale finite-presentation facts and smooth-to-LFP infrastructure, not the full scheme statement; these exact search records are in the node. The item was tested on the empty scheme and on an affine étale map: the conclusion is immediate in both cases, and no extra hypotheses are used.

## Review by K1

I read the item node, its blueprint source reference, and the complete conventions node used by step 1. The cited node says exactly that étale means locally of finite presentation and that finite type is equivalent to quasi-compact plus locally finite type, matching the two quoted passages in `citations.json`. I checked the hypotheses: `U -> X` is quasi-compact by assumption, `X -> Spec K` is quasi-compact and locally finite type because `X` is finite type over `K`, and both properties compose. No new node was created because the composition calculation is a two-line consequence of these definitions. I also checked for an existing project declaration and for duplicate blueprint/DAG statements; none states this item. The only correction to the imported proof was making the composite structure morphism and the two closure properties explicit, and changing the status to `split` with a complete source location.

## What could not be finished

Nothing remains open for this split; the unavailable LeanSearch service is recorded as unavailable in `mathlib_searches`.

## Second reading by K1

- Item statement: checked against the blueprint node `lem-kun-etale-lfp` and the Stacks formulations of locally finite presentation and finite type (Tags 01TO and 01T0); the hypotheses and conclusion agree, including the quasi-compactness hypothesis on $U\to X$.
- Step 1: checked against the complete statement of `def-weil-pbc-scheme-conventions`; its étale clause supplies locally finite presentation and its finite-type clause supplies the quasi-compact plus locally finite-type criterion. The remaining composition and quasi-compactness checks are elementary closure facts, and the step does not use a proof hidden inside the cited node.
- New nodes: none; therefore B1--B7, duplicate-node search, and new-node Mathlib-leaf requirements are vacuous. A whole-DAG search found no existing node duplicating the item and no source node that should be cited in place of the elementary step.
- Edge cases: the empty scheme and an affine étale map over a field satisfy the statement directly; the field case and the cases $n=0,1$ introduce no additional hypotheses (the statement has no coefficient or integer parameter).
- Blueprint metadata: `tools/blueprint_refs.py ancestor/search` gives the item itself as the nearest ancestor and finds no `same_as` match; because this is an imported item, `blueprint.from` remains null as required, while `split_report.blueprint` records the proof location.
- Changed: corrected the second-reading metadata assessment and retained the imported item fields; no mathematical statement or proof step was changed.

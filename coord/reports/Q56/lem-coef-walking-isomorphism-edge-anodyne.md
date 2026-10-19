# Stage-1 report: lem-coef-walking-isomorphism-edge-anodyne

## Files written

- `dag/nodes/sec-six-functors/lem-coef-walking-isomorphism-edge-anodyne.json`: item, split with two proof steps.
- `dag/nodes/sec-six-functors/lem-coef-walking-isomorphism-alternating-horn-filtration.json`: new statement-only node; Mathlib searches found no match.
- `citations.json`: verbatim citations for every node used in every item step.

## Attachments

None. No declaration tagged `(blueprint: lem-coef-walking-isomorphism-edge-anodyne)` or matching the item was found in the read-only Lean source.

## WANTED

WANTED: archival copy of Kerodon Tag 00UG, Subsection 3.1.2, for the horn-generated definition and closure; the special alternating filtration is agent-written because no source or Mathlib declaration states it.

## Not duplicates

- `lem-coef-walking-isomorphism-alternating-horn-filtration` vs `lem-coef-walking-isomorphism-edge-anodyne`: the item asserts the full right lifting property of the forward edge against every Kan fibration, while the new node only states the explicit simplicial-subset horn filtration used to prove that lifting property.
- `lem-coef-walking-isomorphism-alternating-horn-filtration` vs `lem-coef-quasicategory-invertible-interval`: the existing node characterizes isomorphisms in a quasicategory and endpoint evaluation, while the new node states the strictly smaller explicit horn-cell filtration of the ordinary walking-isomorphism nerve.
- `lem-coef-walking-isomorphism-alternating-horn-filtration` vs `lem-coef-edge-inverting-anodyne-extension`: the existing node proves extension of edge-inverting diagrams along an already Kan-anodyne map; the new node constructs the specific filtration proving this map is anodyne.

## What I checked and corrected

I read the imported item, the `sec-six-functors` chapter record, `coord/brief-stage1.md`, `stages/1-dag.md`, and the B–E delivery checklist. I searched the whole DAG, blueprint, and both read-only Lean trees for the item id, its walking-isomorphism terminology, and matching declarations; none attaches. I also read the existing `lem-coef-quasicategory-invertible-interval` proof: its alternating-word filtration appears only inside a proof step, so I did not cite that proof as a theorem. I extracted the filtration into a strictly smaller statement-only node and ran all four required Mathlib searches for that node; the returned nerve and generic horn declarations do not state the filtration.

For item Step 1, I checked the new node's statement line by line: it supplies the forward-edge base, each subsequent pushout horn, and the degreewise union, exactly what the stage-by-stage lift uses. I checked the cited definition node: it defines horns, simplicial sets, and the all-horn Kan lifting condition, so it supports the lifting premise and the final identification. The pushout gluing is the universal property of the displayed attachment, and compatibility follows because each chosen filler extends the previous stage. For Step 2, I verified that the filtration's $J$ and $i$ are exactly the item's ordinary nerve and forward edge, and that the argument stays in the common universe; empty cases are vacuous. I corrected the imported item by adding its proof, proof dependencies, blueprint reference, split report, and the required citation quotes; the mathematical statement itself was unchanged.

The finite base cases were checked directly: stage $J_1$ is the vertices $0,1$ and the arrow $0\to1$; stage $J_2$ adds the reverse edge and the triangle $(0,1,0)$; later stages add alternating words and their first-deleted faces. The opposite starting vertex gives the reversed filtration, though the item only needs the forward one. No new definition, SGA source, Lean code, compiler, Lake, or build was used.

## What was wrong in the imported node or source

The imported node had no proof and its `created.item` referred to another worker's path-reversal item. I retained its existing provenance fields and repaired only this item's proof metadata. The blueprint's source is online and not archived; this is recorded as WANTED. No statement error was found.

## What I could not finish

Nothing beyond the required stage-1 split remains.

## Review by Q56

I read the item source and the new node source, and verified that the item's two steps use only statements actually present in the cited nodes. The first step uses the filtration's exact pushout-horn and union clauses and the definition node's all-horn lifting condition; the second checks the nerve/edge identification and universe convention from those same statements. I checked the hypotheses at each use, including $n\ge2$ for the attached horns, the forward-edge base stage, compatibility of the degreewise union, and vacuous empty cases. I compared the new node against all walking-isomorphism and anodyne nodes found by DAG searches and documented the differences above. The imported statement was preserved verbatim; only the missing split proof and required metadata/citations were supplied.

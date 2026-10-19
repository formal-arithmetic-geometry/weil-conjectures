# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-open-subcollection-map.json`: item split into three elementary proof steps; no new child nodes.
- `citations.json`: empty because all proof steps are direct arguments from the item hypotheses and definitions, with no cited DAG node.

## Attachments

None. No declaration tagged `(blueprint: lem-trf-derived-basis-open-subcollection-map)` or equivalent sorry-free project declaration was found in the source checkouts.

## WANTED

None.

## Not duplicates

No new node was created, so there are no duplicate-node pairs to report. The whole DAG and blueprint were searched for Tag 0D5Q and the quotient-subcollection construction; the only use found is the already-existing parent reference in `lem-trf-derived-basis-local-hom-glue`.

## What was wrong or incomplete

The imported item had an empty proof and an unspecified blueprint location. I supplied the proof and filled the inherited blueprint place. The statement itself agrees with Stacks Tag 0D5Q after specializing the topological-space input to the underlying space of a scheme. The Mathlib searches found only generic quotient and basis APIs, so this remains a natural-language statement rather than a Mathlib leaf.

## What remains unfinished

Nothing in this split. The downstream BBD-descent node cites this construction by its statement.

## Review by Q25

I read the item source at Stacks Project `literature/stacks-project/topology.tex`, Tag 0D5Q (`topology-lemma-create-map-from-subcollection`), including its proof and the preceding basis-topology lemma (Tag 0D5P). I also read the existing downstream use in `lem-trf-derived-basis-local-hom-glue.json` and the inherited blueprint ancestry through `lem-trf-local-term-locality`; the item’s `from.place` now names the exact Tag 0D5Q construction sentence. Step 1 checks the equivalence relation, quotient set, and the equality `f^{-1}(f(U)) = U` directly from the relation, with no extra hypothesis. Step 2 checks `f(U) ∩ f(V) = f(U ∩ V)`, applies the stated intersection-refinement equality, verifies that the images cover the quotient, and explicitly constructs the topology as unions of image sets; this proves the basis claim and finite-intersection closure. Step 3 checks continuity by taking inverse images of arbitrary unions and uses the equality from Step 1; it also covers empty spaces and empty indexing families. I verified that no step relies on a proof hidden in another node, so `citations.json` is correctly empty, and that no new node would be more than a restatement or an elementary subargument. I ran both phrasings of LeanFinder and LeanSearch, two Loogle queries (both invalid due to unknown identifiers, recorded as such), and two Mathlib grep queries; all results were generic topology declarations and none matched the Stacks construction.

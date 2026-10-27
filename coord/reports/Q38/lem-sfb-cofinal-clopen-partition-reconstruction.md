# Q38 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-cofinal-clopen-partition-reconstruction.json`: statement item, now split into six steps; not an exact Mathlib leaf. Statement, statement dependencies and inherited metadata retained. No new nodes and no new Mathlib leaves.
- `citations.json`: the three proof citations, each with its cited node's full statement as a verbatim quotation.
- `searches.jsonl`: actual searches logged by msearch.py; their records were read and appended to the item's inherited Mathlib searches.
- `report.md`: this report.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, cofinal partitions, clopen partitions, and reconstruction-related names found no project declaration stating this item. Existing project declarations concerning clopen partitions address different constructions. No Lean was written or compiled.

## WANTED

None. The source and the supporting topology facts are available locally.

## What was wrong and what changed

The item had a complete true statement but no proof. Stacks Tag 08ZY states reconstruction using all finite clopen partitions; this item's cofinal directed subfamily variant needs the additional explicit arguments now supplied: use cofinality on a separating two-block partition, and use a finite common upper bound to establish the finite intersection property for compatible blocks. The proof does not assume a block exists in an empty partition, does not assume the index set has a greatest element, and does not treat cofinality as equality of diagrams.

No statement dispute, source error, or change of route was necessary. The recorded chapter is sec-six-functors-basics and the inherited unit is sk-thm-sf-ctf-stability (whose unit record belongs to sec-six-functors). I read both records and preserved this metadata. The item is an auxiliary generic topology input to the parent's reconstruction step, not the key statement of either unit. The blueprint ancestor command returns None for the existing created-item chain; the inherited null ancestor and its precise place are retained. Whole-blueprint searches for clopen, partition, totally disconnected, 005D, and 08YE found no equivalent imported statement.

## Unfinished work

None for this stage-1 split. Its three non-elementary inputs are existing Mathlib leaves. Stage 2 and Lean compilation are outside this assignment.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The finite-intersection fact is reused as `lem-sfb-compact-closed-finite-intersection`; clopen separation is obtained from the more general existing `lem-weil-pbc-profinite-clopen-basis`; the homeomorphism criterion is reused as `lem-weil-pbc-compact-hausdorff-bijection`. The existing `lem-sfb-compact-discrete-quotient-realization` quantifies over all discrete quotients, and does not directly state reconstruction for this prescribed cofinal family. No duplicate variant of it is created.

## Mathlib search assessment

The item was searched with LeanFinder twice using different phrasings, Loogle, grep through msearch.py, and LeanSearch. All five calls succeeded; the earlier inherited unavailable LeanSearch result is retained as history, not described as evidence of absence. I read Mathlib/Topology/Category/Profinite/AsLimit.lean, Mathlib/Topology/Category/Profinite/Product.lean and Mathlib/Topology/DiscreteQuotient.lean at the declarations returned. Profinite.asLimit and isoAsLimitConeLift use the diagram of all discrete quotients; exists_of_compat likewise takes a class for every discrete quotient. The Product results use finite subsets of a coordinate set and the restrictions of a compact subset of a product. None is this arbitrary cofinal-partition statement by a one-line specialization, including its explicit singleton-intersection clause. These useful candidates do not justify making the entire item a Mathlib leaf.

## Review by Q38

I read topology.tex Tag 08ZY, label lemma-profinite, particularly the full proof of (2) implies (1). Its construction is exactly the block projection used here. I also read Tag 005D, label lemma-intersection-closed-in-quasi-compact; Tag 08YE, label lemma-bijective-map; Tag 08ZZ, label lemma-profinite-refine-open-covering; and Tag 08ZN, label lemma-connected-component-intersection-compact-Hausdorff. The latter explains the separation input in 08ZY. This split uses the already available stronger clopen-basis statement instead of introducing a second component-intersection lemma. No new node requires a separate source review.

For step 1 I checked the empty space separately: nonempty J supplies an empty coordinate set, making the product and L empty. The empty-index-set exception is therefore excluded exactly by the stated hypothesis. This establishes all conclusions in that case without invoking compactness incorrectly on a nonexistent compatible block.

For step 2 I opened `lem-weil-pbc-profinite-clopen-basis` and checked that its statement gives a clopen neighbourhood inside every prescribed open neighbourhood for a compact Hausdorff totally disconnected space. All three hypotheses are given on P. Hausdorffness provides disjoint neighbourhoods of distinct points; the basis lemma gives a clopen C excluding the second point. Both blocks of the resulting partition are nonempty. Cofinality, with precisely the refinement direction in the item, then separates their J-coordinates.

Step 3 uses only the definitions, with the argument written out: containing-block uniqueness proves compatibility; inverse images of finite-coordinate basic opens are finite intersections of unions of open blocks; distinct tuples are separated by disjoint singleton cylinders in a discrete coordinate. It does not invoke an uncited product or limit separation theorem.

For step 4 I opened `lem-sfb-compact-closed-finite-intersection` and checked that its statement allows any small family of closed subsets in a compact space, with the empty finite intersection equal to the whole space. Closedness and nonemptiness come from the blocks. The common-upper-bound construction starts with an actual index i0 from J and successively uses directedness, so it works also for the empty finite set. Compatibility makes the fine block a subset of every selected coarse block, rather than merely claiming the intersection is nonempty. Its point supplies exactly the finite-intersection hypothesis of the cited node.

Step 5 is an elementary assembly: membership in a block determines its projection, and the previously proved point-separation rules out two points in the same full intersection. It identifies the inverse point explicitly and proves both injectivity and surjectivity without a new lemma restating part of the item.

For step 6 I opened `lem-weil-pbc-compact-hausdorff-bijection`. Its statement concerns subspaces U and V of arbitrary topological spaces; taking the whole spaces P and L supplies exactly the map here. Its assumptions are continuous bijection, quasi-compact source and Hausdorff target, which were given or proved in steps 3 and 5. No compactness of L or closedness of its embedding is needed. I also checked the pinned Mathlib statements: isTopologicalBasis_isClopen / compact_exists_isClopen_in_isOpen in Topology/Separation/Profinite.lean, CompactSpace.iInter_nonempty in Topology/Compactness/Compact.lean, and isHomeomorph_iff_continuous_bijective in Topology/Homeomorph/Lemmas.lean agree with the three cited leaf statements.

Against delivery-errors B, all objects are introduced in the unchanged statement, all new work is proof text, the three sources have their Stacks tags and labels checked, and no new definitions or unsplit nodes conceal proof sketches. Against C, every non-elementary step cites the actual statement used, the quotes in citations.json are copied verbatim, and no dependency returns through the parent. Against D, the proof carries the separation, finite-bound and compatibility arguments itself, using only strictly more general topological tools; no new node restates an item clause. Against E, I checked empty P, singleton P, a two-point discrete space, and a finite discrete space where cofinality forces a refinement of the singleton partition. In each case the block intersection and map have the stated behaviour. All proof steps are below 2000 characters, with no hidden long-step lemma. No hypothesis or conclusion was changed.

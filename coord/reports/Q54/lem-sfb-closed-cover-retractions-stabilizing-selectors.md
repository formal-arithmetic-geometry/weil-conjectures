# Worker report — Q54

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-cover-retractions-stabilizing-selectors.json`: unchanged statement; split in eight steps using two existing Mathlib leaves; no Mathlib match for the entire item.
- `citations.json`: verbatim statement quotes for the two proof citations.
- `searches.jsonl`: the search command's unmodified log, five actual queries.

No new nodes, no new Mathlib leaves. The sandbox initially contained only dispatcher markers. I copied the current live item and retained every inherited search, source, ancestry and other field; there was no older sandbox proof or report to reuse. Only this sandbox was written. No Lean was written or compiled, and no git command was run in the shared repository.

## Attachments

None. Exact blueprint-id, retraction, stabilizing-selector and clopen-partition searches of `lean/WeilConjectures/` found no declaration stating the item. The PiNat declaration is Mathlib, not a project attachment, and already has a DAG leaf.

## Wanted sources

WANTED: an exact published reference for the combined closed-cover retractions and eventually least-index selectors, for lem-sfb-closed-cover-retractions-stabilizing-selectors. This is the inherited request, not an assertion that the blueprint supplies a missing theorem. Stacks topology.tex Tag 08ZZ (`lemma-profinite-refine-open-covering`) and pinned Mathlib PiNat.lean supply the two non-elementary ingredients; the intervening argument is written out by Q54 and marked agent-origin.

## What changed and why

The live item was statement-only. I read its originating Q49 report, especially inherited steps 5–6, and followed that argument. Refining finite Boolean partitions supply the atom embedding; the existing countable discrete-product theorem supplies retractions; decreasing clopen neighbourhoods and a finite maximum supply stabilization. I made the metric constants explicit to prove a strict diameter bound, and replaced the compact-image-closed shorthand with the direct finite-coordinate open-cylinder proof. This avoids silently importing a closed-map theorem. Neither the statement nor its hypotheses required correction. There is no STATEMENT-DISPUTED claim.

The current main-20261015 chapter and `sk-thm-sf-ctf-stability` unit were read, including direct-images proof paragraph (3). That paragraph concerns open direct images; it does not assert this auxiliary topology lemma. The ancestry command returns `None`, as inherited from the analytic chain; I preserved that anchor and its exact source place instead of inventing a blueprint ancestor or changing the unit route. No unit realization field belongs to this item.

## Not duplicates

No new nodes were created. Whole-DAG statement/title searches for finite clopen partitions, clopen bases, closed-product retractions, metrizable totally disconnected spaces and compact embedding facts found the existing leaves used here. In particular, `lem-sfb-countable-discrete-product-closed-retraction` is exactly the product retraction input; its presence rules out creating another retraction node. `lem-weil-pbc-profinite-clopen-basis` supplies precisely the neighbourhood refinement needed. The cofinal-clopen-partition reconstruction node has a stronger cofinal-family setup; its statement was read, but neither its proof nor any unstated consequence is used. The compact-Hausdorff-bijection leaf was also read; the direct inverse-continuity proof makes citing it unnecessary.

Whole-blueprint searches `clopen`, `retraction`, `selector` and `metrizable` found no imported node stating the combined item. The first two return covering/scheme or algebraic retraction nodes; the latter two return no hits. Thus `blueprint.same_as` remains empty.

## Search results

Five fresh actual searches are appended without discarding Q49's inherited searches: two distinct LeanFinder phrasings, Loogle `PiNat.exists_retraction_subtype_of_isClosed`, a whole-Mathlib grep for closed/clopen retractions and selections, and LeanSearch for the complete closed-cover selector assertion. All services answered. The natural-language hits give finite clopen approximations, the countable-product retraction, Cantor-set images, or compact-exhaustion indices. None gives every clause of this item as a one-line specialization. The Loogle hit is exact for the already existing product-retraction leaf, not for this item.

I read the pinned source at PiNat.lean:342 and 673–687, including the subtype theorem at 680, and Profinite.lean:43–79, including the clopen-basis theorem at 66 and pointwise version at 76. These confirm the hypotheses and interfaces used below. The logged search summaries are retained verbatim as the `results` objects; the verdicts distinguish the full item from these partial ingredients.

## Review by Q54

I reviewed the node, all eight proof steps, both cited node statements, the current blueprint direct-images paragraph (3), the originating Q49 report's topology argument, Stacks topology.tex Tags 08ZY (`lemma-profinite`) and 08ZZ (`lemma-profinite-refine-open-covering`), and the pinned Mathlib source places above. Tags were checked against the local tags table. The item is the same compact metrizable Hausdorff totally disconnected space and nonempty closed cover throughout. The compatible metric is only used for the mesh and neighbourhood argument. No finiteness of the cover, openness of its members, or pairwise disjointness is introduced.

1. Step 1 cites `lem-weil-pbc-profinite-clopen-basis`. Its statement explicitly gives, for an arbitrary point of an open set in a compact Hausdorff totally disconnected space, a clopen neighbourhood inside that set. These are exactly the hypotheses on S. Balls of radius `2^{-i}/3` are open; compactness of S makes each chosen clopen cover finite. The explicitly described Boolean atoms are nonempty after discarding empty intersections, disjoint, clopen, exhaustive and refining. Containment in a covering ball bounds the diameter by `2*2^{-i}/3`, strictly less than `2^{-i}`. There is no appeal to the proof of the cited node.
2. Step 2 has no external citation: coordinate cylinders pull back to the named atoms, and finite intersections give product continuity by definition. Equal atom coordinates force distances below every `2^{-i}`, proving injectivity. These are direct calculations from step 1 and the product topology.
3. Step 3 has no external citation: for an arbitrary open neighbourhood of s, one sufficiently small atom lies inside a metric ball contained in it. Its relative coordinate cylinder proves inverse continuity. This does not require a separately imported compact-to-Hausdorff homeomorphism assertion.
4. Step 4 has no external citation: for x outside e(A_j), coordinate-mismatch opens together with S minus A_j cover S. A finite subcover yields an explicit cylinder about x missing e(A_j). The openness of S minus A_j uses exactly its stated closedness. This is a direct use of compactness's finite-subcover definition, not an uncited compact-image theorem. Nonemptiness of A_j supplies nonemptiness of its image.
5. Step 5 cites `lem-sfb-countable-discrete-product-closed-retraction`. Its statement gives a continuous surjection from any countable product of discrete spaces onto any nonempty closed subset, fixing that subset. Step 4 verifies closedness in the entire product, not just e(S), and nonemptiness. Reindexing positive integers by n+1 is bijective, and the factors have the specified discrete topology. Restricting the homeomorphism and composing its inverse with the retraction gives the actual S-to-A_j map, with the fixing identity calculated. No general theorem about arbitrary nonmetrizable profinite retractions is claimed.
6. Step 6 has no external citation: finite unions preserve clopenness, a child atom meeting A_j has a parent meeting it, and an open ball about a point of S minus A_j eventually contains its shrinking atom. Hence the exact intersection equals A_j, not merely its closure or a neighbourhood of it.
7. Step 7 has no external citation: every membership test uses a union of atoms of the same finite partition. The least eligible index and the fallback are consequently constant on each open atom. This proves local constancy also when no index is eligible.
8. Step 8 has no external citation: existence of the least covering index is ordinary well-ordering of positive integers. For a fixed s there are only finitely many smaller indices; choose their exclusion levels and take the displayed finite maximum together with j(s). Decreasingness makes the exclusions permanent, and the true covering index remains eligible. This gives eventual equality at that s and provides no uniform bound.

The only proof citations are in steps 1 and 5, and `citations.json` quotes their statements verbatim. `proof_deps` is exactly their union. The first leaf belongs to another unit but is a Mathlib fact about the same topological spaces; no unapproved off-unit theorem route is used. The other leaf belongs to this item's unit. I inspected B1–B10: there are no new-node form, source, definition, duplication, attachment or Mathlib-leaf obligations to defer. C1–C8 are checked by the step-by-step reasoning above: the argument uses cited statements only, no proof-internal construction, no missing lifting or compactness theorem, and no edge back to a descendant. D1–D5 are met by retaining the actual construction in the parent, rather than moving any clause into a new node. E1–E7 revealed no false or ill-typed statement or suppressed hypothesis.

Small cases: for a singleton S every partition is the single atom and every nonempty A_j is S, so k_i=1 and all retractions are the identity. The argument permits repeated and overlapping A_j, and A_j=S gives U_{j,i}=S. When j(s)=1 the exclusion set is empty and the maximum remains defined. When the first i sets miss an atom, the default 1 still gives a locally constant map. Nonuniformity is essential: take S={0} union {1/n:n>=1}, A_1={0}, and A_{n+1}={1/n}. Each A_j is nonempty closed and the cover is exhaustive, but for every i some point has least covering index greater than i, so k_i cannot already equal the least index everywhere. The proof never assumes otherwise. Empty S and empty A_j are excluded by the actual statement, exactly as needed for the retraction leaf.

There was no previous attempt or return to repair. I corrected the inherited implicit radius choice to the explicit one-third radius and expanded both the embedding and finite-index exclusion details before signing this review. No step exceeds 2000 characters (the longest is 823); no long step hides a separate comparison lemma. All remaining uncited arguments are the displayed finite set, metric or open-cover calculations, so no new task is warranted.

## Unfinished work

No mathematical work on this one-level split remains. The inherited request for an external combined reference remains WANTED; the complete agent argument is now in the item. Delivery validation is the required server dry run followed by direct push.

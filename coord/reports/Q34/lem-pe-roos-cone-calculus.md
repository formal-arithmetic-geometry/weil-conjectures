# Stage-1 delivery: lem-pe-roos-cone-calculus

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-roos-cone-calculus.json`: statement item, now split in eight steps. Its full statement and statement dependencies are unchanged. The existing proof inputs suffice: no new nodes and no new Mathlib leaves.
- `citations.json`: 18 entries, one for each step/node citation, containing the cited statement verbatim.
- `searches.jsonl`: the actual search-command log. `write_split.py` is sandbox-only working material, not a library change.

The item retains its existing source, creation metadata, chapter, unit and blueprint provenance. Its blueprint `same_as` was already empty and remains empty after the searches. This is not the unit's key statement, so no unit realization fields are changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, item id, Roos/roos and cone-calculus concepts. The existing Roos construction/comparison files and shift comparisons do not supply a project declaration giving all clauses of this strict double-cone and augmentation statement. No attachment is asserted from a partial result or a sorried declaration.

## WANTED

None. All sources used are present locally.

## Defects and corrections

The item was unsplit, with no proof. Its coordinate formulas are correct with the declared cochain-cone convention; no statement correction or dispute was necessary. The blueprint's short phrase that the construction commutes with cones and shifts needs the explicit differential, inverse, boundary and augmentation calculations now in steps 4-8. In particular, the cone comparison negates its fourth coordinate, and the cone boundary in the cited derived-category definition is minus the projection. Neither sign may be dropped.

A potentially unnecessary new lemma was avoided: the existing `lem-pe-roos-coordinates-quasi-iso` allows an arbitrary chain endomorphism. Taking that endomorphism to be minus the item's one-minus-transition map gives precisely the differential needed here. There is no need for a new cone-comparison quasi-isomorphism node or a separate five-lemma application.

## Unfinished work

None for this one-level stage-1 split. No Lean was written, compiled or built. Existing dependency nodes retain their own status; this delivery does not claim to complete proofs below them.

## Searches and reuse

Read the chapter `sec-proetale-coefficients`, unit `sk-lem-pe-derived-nakayama`, and the Cones paragraph of the current main-20261015 blueprint proof of `det-pe-derived-nakayama-first-reduction`. The unit route explicitly uses exact pro-etale products for the termwise fibre construction. The existing `det-pe-products-derived` states both the actual derived-product identification and preservation of products of quasi-isomorphisms, for arbitrary ring sheaves and unbounded complexes. It is declared as a generic tool use in `split_report.tool_uses`, since its unit is `sk-prop-pe-products`; the source blueprint explicitly calls for that input. The coordinate quasi-isomorphism node belongs to `sk-def-pe-derived-completion`, already on this unit's route.

Ran `tools/blueprint_refs.py ancestor lem-pe-roos-cone-calculus` and searches for Roos, products, cone and shift, and searched the DAG by those notions and by tags 07KC/08TC. The nearest blueprint ancestor is `det-pe-derived-nakayama-first-reduction`, already recorded on the item. Existing nodes for products, arbitrary coordinate quasi-isomorphisms and native Roos shifts were inspected; none is a duplicate of the entire item. The proof uses the generic coordinate lemma directly and proves the elementary formula identities in its own steps.

Ran all four prescribed Mathlib search kinds through `batch2/msearch.py`, with a second LeanFinder phrasing. All services answered successfully. Their actual hits are in `searches.jsonl`, and the item's added entries reproduce the tool and query text exactly. Read Mathlib's `MappingCone.lean` lines 620-650 and `MappingCocone.lean` lines 29-60: the additive-functor cone comparison and mapping-cocone definitions do not state the complete strict Roos double-cone, coherence and augmentation assertion. The generic exact-product hits alone do not give it either. The inherited searches were retained.

## Not duplicates

No new nodes are proposed, so there are no new-node/existing-node pairs to distinguish. Existing general statements are cited rather than restated as leaves or new lemmas.

## Review by Q34

I read the item's full statement against its current blueprint Cones paragraph. For conventions I read Stacks `derived.tex`, Tag 014E (`definition-cone`), Tag 014Q (`definition-distinguished-triangle`, including the subsequent explicit minus-projection cone triangle), Tag 08TC (`definition-derived-limit`), Tag 07KC (`lemma-products`, statement and proof); and `homology.tex`, Tag 011G (`definition-shift-cochain`). I also read the current blueprint derived-products statement and its proof. This supplies the literature route; the detailed strict coordinate argument is explicitly marked as agent-written. There are no new nodes needing additional sources. No SGA route is used.

For step 1 I opened `det-pe-products-derived`, `def-weil-category-product`, `def-weil-abstract-derived-category` and `def-weil-inverse-system`. They supply respectively the termwise product, its projection universal property, the actual cochain/cone/shift definitions, and strict transition-map compatibility. The calculation uses only those definitions: the square of the differential cancels because the transitions are chain maps, and identity, composition and addition hold after each projection. All objects lie in the abelian category of modules over the given ring sheaf, on the small site in the statement's existing conventions. No commutativity, boundedness or surjectivity is assumed.

For step 2 I opened the full statement of `lem-pe-roos-coordinates-quasi-iso`. Its arbitrary endomorphisms can be chosen as `-s_N` and `-s_N'`; its differential then agrees exactly with the item's negative-coupling fibre differential. The diagonal map is a chain map by step 1. The last clause of `det-pe-products-derived` gives its quasi-isomorphism hypothesis on the product map. Thus the cited statements give exactly the two non-elementary facts used, with no appeal to the proofs of those nodes.

For step 3 I rechecked the first clause of `det-pe-products-derived`: it retains the actual product and projections after localization, not merely some isomorphic object. That makes the localized one-minus-transition map the required one. `def-weil-abstract-derived-category` explicitly states the cone triangle with boundary `-p`, and `def-weil-triangulated-category` explicitly states TR2. Inverse rotation makes the first map the positive first-coordinate projection and gives precisely the triangle required in `def-weil-derived-limit`. This asserts a derived limit together with a triangle, not uniqueness of a chosen functor on arbitrary triangulated towers.

For step 4 I checked both differentials after setting epsilon equal to (-1)^r, the inverse, naturality on diagonal maps, the identity at r=0, and the r+s multiplication law. Only the shift convention and product universal property are used. The same calculation works for negative integers.

For step 5 I constructed both directions of the product/binary-biproduct identification from projections, then wrote the source and target four-component differentials. Substitution gives the same four components on both sides of the proposed comparison. The displayed inverse really is an inverse. This is one elementary matrix calculation, not an unproved theorem that a newly introduced node would simply restate.

For step 6 I checked naturality on an arbitrary strict commutative square. I checked the actual cone inclusion and, separately, the boundary: applying H(-p) and then the shift comparison gives (-a,a'), exactly minus the target cone projection. This removes any ambiguity hidden in the words 'preserves the boundary'. It uses the convention written in the cited definition, not a different cone convention from a source-library API.

For step 7 I checked s_N J=0 by every projection, and then the chain-map identity for the zero-second-coordinate augmentation. The naturality square follows from the given strict augmentation compatibility, again after every projection. For step 8 I evaluated both cone augmentations on (m',m); each becomes ((J'm',0),(Jm,0)) after the comparison. For shifts the second coordinate remains zero. These are equalities of the specified comparison maps, not choices supplied by a triangulated completion axiom.

I tested the formulas with zero complexes and zero ring sheaves, the empty scheme, zero and identity tower maps, constant towers, and towers with zero transitions; none requires an extra hypothesis. At r=0 the comparison is the identity; at odd positive or negative r the second-coordinate sign is essential; in characteristic two the same formulas specialize correctly. The only potentially infinite operation is the existing countable product theorem, which already applies to unbounded complexes over arbitrary ring sheaves. Each new proof step is shorter than 2000 characters. The long-step hidden-lemma check therefore has no flagged step; the only non-elementary comparisons are precisely the two existing cited statements in step 2.

I checked delivery-errors B-E against the delivered JSON: no unsplit new-node proofs, no new undefined notions, no duplicate nodes, no clause relabelled as a new lemma, no source-only citations in place of arguments, no extra hypotheses, and no missing compatibility argument. Every `uses` entry has a verbatim statement quote in `citations.json`; every cited node was opened and its statement read. The proof-dependency list is exactly the union of those entries.

The preliminary server `check_dag` reports no finding introduced by the sandbox or on its nodes. The preliminary server `review_split` reports PASS, 0 new nodes, and the informational observation that the enclosing unit has no realization recorded yet. This non-key item does not own that unit realization work. The full dry run and push follow this review.

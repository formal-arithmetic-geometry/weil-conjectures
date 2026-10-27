# Worker report

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-big-etale-higher-image-base-change.json: statement, split; not a Mathlib leaf. Statement and its seven statement dependencies unchanged. Two proof steps, with only the existing derived-form node as proof dependency.
- citations.json: verbatim statement extracts for both steps.
- report.md: this report. No new nodes, no new Mathlib leaves, no unit record changed.

## Attachments
None. Searches of lean/WeilConjectures for the exact blueprint id, big-etale terminology and stack/higher-direct-image combinations found no theorem stating this item. The generic project theorem CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso is only the cohomology-commutation ingredient, not an attachment for stack base change.

## WANTED
None.

## Corrections and remaining work
The item was unsplit and its seeded proof dependency was already the correct derived-form node. No statement dispute was found, and the statement was not changed. The derived node remains an unsplit prerequisite; this is a one-level split, not a claim that its Lean proof is complete. The ancestry utility returns None for blueprint.from.node; this pre-existing null and the detailed from.place and via chain are retained, not replaced by an invented ancestor. The latest blueprint direct-images proof (3) and the unit/chapter records were read; the support lemma does not realize the unit's key statement, so realized fields are untouched.

## Mathlib and duplicate searches
Fresh msearch.py calls (LeanFinder twice with distinct phrasings, Loogle, grep, LeanSearch) are recorded verbatim in searches.jsonl and appended to the item's existing search history. All services answered. The hits are sheaf functor composition, ordinary scheme module pullback and stability of etale morphisms under base change; none states derived or higher direct image base change on the big sites of arbitrary algebraic stacks. I read the composition declarations and the generic project homology-commutation declaration. DAG searches by Tag 075H and big-etale/base-change terms found the existing derived-form node and the sibling fibre-cohomology and restriction lemmas. Whole-blueprint searches for 075H, big etale, precomposition and higher direct images did not find this statement elsewhere.

## Not duplicates
No new nodes. The item is deliberately the per-degree consequence of lem-sfb-stack-big-etale-derived-base-change, as prescribed by the derived-form convention. The representable-restriction nodes concern restriction to small scheme sites and impose representability; they do not replace arbitrary stack base change on the big sites.

## Review by Q59
I read the item, the full statement of lem-sfb-stack-big-etale-derived-base-change, the statements of all seven definition dependencies, and Stacks stacks-sheaves.tex Tag 075H (lemma-base-change-higher-direct-images), including its proof and its preceding restriction formula. Tag 075H covers algebraic stacks, arbitrary 2-Cartesian squares and module sheaves for the etale topology. In particular this is the big stack site, not the small etale site of a scheme or a quasi-coherent derived category. The exactness here is precomposition along a stack functor and does not assume that the morphism of schemes is flat.

Step 1 cites the derived node for exactly its asserted canonical natural derived isomorphism and its exact termwise precomposition functors. Its source and target, coefficient structure sheaves, arbitrary stack morphisms and degree-zero module F agree verbatim with this item. There is no representability, smoothness, flatness, qcqs or quasi-coherence premise to check. Step 2 uses the same node only for exactness and the isomorphism already obtained in step 1. I wrote out cycles, boundaries and their quotient, then identified H^i of the injective-resolution direct images with R^i. The map is H^i of the canonical derived comparison under this functorial identification; applying H^i to its inverse proves invertibility. This is a two-line exact-functor calculation expanded for readability, not a new lemma node. The sole non-elementary prerequisite remains the existing derived-form node, as required by the per-degree convention. Both citation quotes are exact substrings of that node's statement.

I checked B-E of delivery-errors.md: no new statement-only or leaf nodes to audit, no relabelling of the item in a new node, no hidden acyclicity or injective-preservation assertion, no use of a cited proof rather than its statement, and no new hypotheses. Both steps are under 2000 characters. Small cases: i=0 gives the ordinary big-site fibre-product comparison; F=0 and the empty source give zero objects; identity base change gives the identity comparison; non-flat base change is covered because pullback means precomposition and has the exactness explicitly asserted by the derived node. Arbitrarily high i requires no cohomological dimension bound, since an isomorphism remains an isomorphism under each cohomology functor. No SGA source is used. Nothing mathematical was left unfinished beyond the existing unsplit derived prerequisite.

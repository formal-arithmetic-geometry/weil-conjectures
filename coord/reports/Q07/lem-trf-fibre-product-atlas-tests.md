# Worker report: lem-trf-fibre-product-atlas-tests

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fibre-product-atlas-tests.json: the assigned statement, now split into six proof steps; no exact Mathlib match.
- citations.json: nine verbatim statement quotations, one for every step/dependency incidence.
- report.md: this report. searches.jsonl is maintained by the authorized search command.

New nodes: 0. New Mathlib leaves: 0. The item was unsplit in the repository, and the sandbox initially held no item or report. The copied statement and all fields reserved to the maintainer are unchanged.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, fibre/fiber-product atlas names, representable diagonals and etale atlases. There is no project declaration giving the entire statement. Mathlib search hits about scheme pullbacks, etale stability and Zariski gluing do not prove the sheaf-level atlas and its explicit scheme-test identifications.

## WANTED

None. All mathematical sources used are available locally.

## Corrections to the imported material

The item had a complete, correct statement but no proof or proof dependencies. The missing content is supplied directly, rather than moved into new clause-shaped nodes. The existing covering-base-change and covering-composition nodes suffice for the non-elementary geometry. In particular, no extra representability/permanence lemma or categorical pullback reassociation node is necessary: the actual section bijections are written into steps 2 and 4.

No statement dispute was found. The original statement requires only the diagonal of H to be representable; the proof never assumes representability of the diagonals of F or G, nor that F, G or H themselves have scheme atlases beyond the two maps explicitly assumed.

## Unfinished work

None for this one-level split. No Lean was written or compiled, and no repository or launcher file was changed.

## Blueprint and duplicate searches

Read dag/chapters/sec-trace-formula.json and dag/units/sk-i-curve-zero.json, as well as the main-20261015 statement and proof of lem-trf-local-term-locality. The atlas lemma is a lower-level tool on the historical polarized-descent chain recorded in its inherited blueprint.from field; it is not the key node realizing the unit statement. The unit record therefore needs no edit.

Ran tools/blueprint_refs.py ancestor on the item and searches for 'representable diagonal', 'surjective etale', 'base change', 'fibre product atlas', and 'etale covering'. Searched the whole DAG for Tag 04T9, its exact Stacks label, representable-transformation permanence labels, and titles/statements concerning Yoneda, etale base change and composition. Read the neighboring sheaf-pullback diagonal and parent fibre-product nodes and the stack-atlas calculus candidates. The former needs extra diagonal hypotheses and the parent depends on this item; neither is used circularly. The stack results concern 2-fibre products and representability by algebraic spaces, not this scheme-test calculation. There is no reason to introduce another node. Existing generic scheme permanence nodes are cited.

## Mathlib searches

The five new recorded searches were run through msearch.py and their actual hits read: grep and Loogle returned no hits; LeanSearch returned scheme-pullback, scheme-Etale and base-change results; two LeanFinder phrasings returned scheme-pullback/gluing and generic jointly-surjective/etale results. Their exact queries and top hits are copied from searches.jsonl into mathlib_searches. Inherited searches are retained. I read Mathlib/AlgebraicGeometry/Morphisms/Etale.lean (including etale_comp and etale_isStableUnderBaseChange), Sites/MorphismProperty.lean (singleton/ofArrows membership and covering permanence), and CategoryTheory/Yoneda.lean (fullyFaithful). They support the generic tool nodes already in the DAG; they do not constitute a one-line proof of the whole item.

## Review by Q07

I read Stacks spaces.tex, Tag 04T9, label lemma-fibre-product-spaces-over-sheaf-with-representable-diagonal, including its complete proof and especially the last paragraph constructing U times_H V. I also read morphisms.tex, Tag 02GO (lemma-base-change-etale), Tag 01S1 (lemma-base-change-surjective), Tag 02GN (lemma-composition-etale), topologies.tex Tag 0217 (lemma-etale), and categories.tex Tag 001P (lemma-yoneda). There are no new nodes needing separate source reviews. The proof expands the atlas paragraph's two permanence applications into concrete arbitrary-scheme tests; it does not use the separate diagonal assertion of the algebraic-space fibre-product theorem.

For step 1, I checked the full statement of def-weil-pbc-sites-and-cohomology: its equalizer condition is exactly the unique gluing and local equality test used. The pairs glue in F and G, and equality of their images is checked in H. This is an explicit sheaf-axiom argument, not an uncited theorem about limits of sheaves.

For step 2, I checked def-pc-fibre-product for the actual universal property on arbitrary test schemes, and def-trf-algebraic-space for the definition of representability by schemes. The base of the diagonal test is Z = U times_S V, a scheme by the former node. The additional H-section is uniquely forced by the two images, so deleting and reinserting it gives the claimed natural bijection. This proves representability of W without invoking a new lemma that restates the item.

For step 3, the statement of def-trf-algebraic-space explicitly includes all scheme-test properties. Applying the hypotheses on a and b to the chosen maps x and y gives both A, B and their surjective etale scheme projections. I read lem-galois-yoneda-fully-faithful, whose statement is the natural-transformation/morphism bijection, and apply it in the category of S-schemes to obtain alpha and beta. I do not use the fully-faithful node as if it stated the more general Hom(h_T,F) evaluation theorem.

For step 4, the sole extra fact is the universal property actually stated in def-pc-fibre-product. For any R, both sides describe exactly the same triple (tau,u,v); the H-compatibility is forced by f x = g y. The two inverse assignments and their restriction behavior are explicit. Keeping the common tau shows the isomorphism is over T and identifies its projection with beta after pr_B. No internal construction from the proof of a cited node is used.

For step 5, I read the entire statement of lem-weil-pbc-etale-covering-base-change: it permits an arbitrary scheme base-change map and concludes both etaleness and joint surjectivity. Its singleton specialization applies because alpha is surjective etale, with no qc, separatedness or finite-type hypothesis. The base change is along beta and its projection goes to B, so the order of the factors is correct.

For step 6, I read lem-weil-pbc-etale-covering-composition: its final sentence explicitly asserts the two properties for a composite of two surjective etale morphisms. Both hypotheses were established in steps 3 and 5. The definition node then turns the arbitrary scheme tests into precisely the three properties asserted for w. These two geometry lemmas are Mathlib leaves, hence do not require a route exception or a new tool_uses entry.

I checked delivery-errors B through E against these files. All objects are introduced, dependency quotations are verbatim, uses and proof_deps agree, there is no new unsplit node carrying a proof, and no extra axiom or geometric hypothesis is assumed. Every elementary step spells out its inverse maps or gluing argument; the non-elementary permanence results have cited statement nodes. No step is longer than 2000 characters. There is no inline hidden comparison lemma: the two comparisons are directly the universal-property calculations the item asks to prove.

As edge cases I checked T empty (A, B and A times_T B are empty and the unique maps to the empty scheme are surjective etale), identity atlases, and F or G empty (a test map forces T and its tests to be empty). Distinct lifts are retained as distinct pairs, so no monomorphism or injectivity of an atlas is assumed. Equalities are equalities in sheaves of sets, not isomorphisms in stacks; no 2-categorical compatibility is missing. The calculations remain valid for non-separated schemes and non-quasi-compact atlases. Neither source errors nor statement repairs were needed.

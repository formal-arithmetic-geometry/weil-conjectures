## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-fibre-product-separated-comparison.json`: split into four steps; no Mathlib match. Retained the sandbox's previous argument and all ten search records; added an explicit definition citation in step 4 and repaired the inherited null blueprint ancestor.
- `citations.json`: eight step/node entries, each quote checked verbatim against the current repository statement.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, library files, launcher files, chapter records or unit records were changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and item id, `fibreProductAfterMap`, fibre-product-after-map, stack comparison, `AlgebraicStack`, `DeligneMumford` and `GroupoidTwoFiberProduct`. No declaration there states the item. Hits mentioning separatedness and Stacks are scheme results or source references, not this theorem about 2-fibre products of stacks. A definition or a sorry declaration would not establish an attachment.

## WANTED

None for this split. All sources actually used are present under `literature/stacks-project/`.

## Source, route, and corrections

Read Stacks `stacks-morphisms.tex`, Tag 050H, label `lemma-fibre-product-after-map`, including its displayed square and proof. Its representability assertion and clause (3) give exactly the comparison and separatedness requested here; the other clauses (local finite type, unramifiedness, properness, and quasi-compactness) are not clauses of this item. Read `algebraic.tex`, Tags 04X5 and 04X6, labels `lemma-category-of-spaces-over-smaller-base-scheme` and `definition-viewed-as`, for viewing stacks over the integers. Verified all three tag/label associations against `tags/tags`.

Read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit statement and direct-images proof. Paragraph (3) treats proper and open direct images. This auxiliary comparison belongs to the inherited alteration/moduli branch below that paragraph; this delivery does not replace a unit step or change its route. The item is not the unit's key statement, so no realization record is written. All proof citations are definitions or belong to `sk-thm-sf-ctf-stability`; no off-route tool permission is needed.

The earlier sandbox already contained a valid four-step argument, citations and logged searches but no report. I preserved those materials and compared the item with the current repository, where it remains unsplit. The server review_split check on that earlier argument passed. I then made explicit the definition converting a DM stack with its smooth atlas into an algebraic stack, rather than leaving that definition implicit in step 4.

The inherited `blueprint.from.node` was null although `from.place` names `det-thm-sf-ctf-stability-direct-images`. `blueprint_refs.py ancestor` follows the old creation chain to a Lean module and returns None. The cited general groupoid-identity node and moduli-definition node already repair that chain to the genuine blueprint node named in the place. This delivery makes the same metadata correction, preserving the via chain, chapter, unit and mathematical statement. The latest blueprint proof was checked, rather than an old snapshot.

No mathematical statement dispute was found. In the absolute clause the separatedness condition is on the absolute diagonal. Relative separatedness is not silently used as a proof that the absolute diagonal is separated when the base is arbitrary.

## Searches and reuse

Read `searches.jsonl` and the ten search records already in the sandbox item. Five are inherited from the live item and five are logged for Q158. They include LeanFinder with two different fibre-product phrasings and an isomorphism-sheaf phrasing, LeanSearch, Loogle, and grep. No search was invented or rerun merely because an earlier session ended. The hits concern scheme separatedness, ordinary categorical pullbacks, products, or sheaf isomorphisms, rather than this representable separated morphism of stacks.

Read the actual candidate source at Mathlib `CategoryTheory/Limits/Shapes/Diagonal.lean:309` (`pullback_map_diagonal_isPullback`) and `AlgebraicGeometry/Morphisms/Separated.lean:131` (the scheme comparison closed immersion). Ordinary categorical pullbacks are not the groupoid 2-pullbacks here, and scheme morphisms do not specialize in one line to arbitrary DM stacks. Also inspected the recorded scheme cancellation candidate in `AlgebraicGeometry/Morphisms/Proper.lean:124`; it supplies no stack comparison. No search service outage was recorded as absence.

DAG searches covered 050H, fibre-product-after-map and separated-comparison terminology. Whole-blueprint searches for `fibre product`, `050H`, and `separated comparison` found no imported node stating this item. The already existing `lem-sfb-groupoid-diagonal-two-pullback-identities` does supply the general groupoid identity and is reused. The existing separation-permanence node is over a field and concerns stability and composition; the separation-composition node concerns proper relative diagonals. Neither supplies a reason to create another comparison node.

## Not duplicates

No new nodes were created. The more general groupoid identity supplies only the 2-cartesian square; the present item additionally applies diagonal representability and checks separatedness on scheme tests, including the absolute interpretation. Existing nodes are cited, not duplicated. In particular no clause of this item was moved to a newly named node.

## Review by Q158

I read the sources above and the complete statements of every cited node with the proof steps open. The base S is arbitrary throughout, and no finite-type, properness, separated-base or atlas-choice hypothesis is inserted.

Step 1 uses clause (2) of `lem-sfb-groupoid-diagonal-two-pullback-identities`, not a statement about an ordinary categorical pullback. Its u, v, h, D specialize respectively to a, b, Z to S, and the discrete represented groupoid of S. The stated upper comparison applies h to the structural isomorphism, exactly the forgetting map j. Its left map is a composed with the X projection, and its commutativity isomorphism is the structural a(x) to b(y) isomorphism. The cited node imposes no additional stack, atlas or finiteness conditions.

Step 2 uses exactly the representable-diagonal clause of `def-sfb-stable-pointed-moduli-groupoids` and exactly arbitrary 2-base-change stability of representability in `lem-sfb-fibred-groupoid-representable-smooth-calculus`. Both statements were opened. The latter expressly allows any base-changing fibred groupoid without assuming it is algebraic. Hence no unstated algebraicity theorem for R is needed. For each scheme T to R, the displayed E_T equivalence is the universal property of the square already established in step 1; it is over T, not only an equivalence of unbased groupoids.

Step 3 is elementary: compose the given scheme test T to R with (a,b), apply the hypothesis defining separatedness of the diagonal to that very test, and identify its resulting algebraic-space map with E_T to T from step 2. Diagonals are identified over T under this equivalence, so the closed-immersion assertion is precisely the required one. This is a substitution into the hypothesis, not an uncited general separated-base-change theorem or an appeal to a proof hidden in another node.

Step 4 uses the DM definition for etale descent, representable diagonal and an etale surjective atlas; the calculus node explicitly says that a representable etale map is smooth. I added `def-sfb-algebraic-moduli-stack`, whose statement calls just these data an algebraic stack. Part (1) of `lem-sfb-algebraic-stack-change-base-to-integers` then explicitly guarantees an algebraic stack over Spec Z, hence a representable absolute diagonal. The general groupoid identity applies again over that base, and the same scheme tests prove the absolute comparison and its conditional separatedness. No claim that S is separated or that absolute separatedness follows from relative separatedness is made. The conversion uses the project's etale-descent definition of an algebraic stack, which I checked in that definition node.

For edge cases I checked empty fibres (the assertions are vacuous), discrete scheme groupoids (the square is the familiar diagonal pullback), and X = Y = Spec k mapping to BG for a nontrivial finite constant group G. The comparison is the isomorphism torsor G to Spec k, not a singleton; it is separated, as the statement requires. Thus the argument retains automorphism data. With a nonseparated base the proof still uses only scheme tests and keeps relative and absolute diagonal hypotheses distinct.

Against delivery-errors B--E: there are no new nodes to carry an illicit proof or duplicate lemma; the item is self-contained, TeX has no doubled command escapes, tags and labels were read, and all statement notions remain defined by the unchanged statement dependencies. Every non-elementary fact is supplied by one of the opened cited statements, each quoted verbatim in citations.json; there is no appeal to a cited node's proof. The groupoid identity and representability calculus are reused rather than restated as new clauses. All four step texts are shorter than 2000 characters, and I found no hidden non-elementary subclaim. The mathematical statement and all its clauses are unchanged. No SGA source is used.

## Unfinished work

None in this one-level split. The cited nodes retain their own stage status and are not asserted here to have completed Lean proofs. Acceptance of this delivery is by the independent maintainer review after the required server preflight.

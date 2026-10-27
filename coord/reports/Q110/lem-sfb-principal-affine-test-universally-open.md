# Stage-1 report: lem-sfb-principal-affine-test-universally-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-principal-affine-test-universally-open.json — statement; split in four steps, unchanged statement and statement dependencies; no single exact Mathlib match.
- citations.json — one exact statement quotation for each citation of each proof step.
- searches.jsonl — seven actual Mathlib searches through msearch.py, with results read and seven corresponding records appended to the item.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. All four nontrivial geometric/basis ingredients already have Mathlib-leaf nodes in the DAG. The elementary image and union arguments are proof steps, not nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for UniversallyOpen/universallyOpen and the principal-affine/base-change concepts. There is no exact declaration for this item. The local-isomorphism and flat finite-presentation results have extra hypotheses; they do not attach. The Sheaf PolynomialTestUniversallyOpen source is a separate parent statement with sorry, not a closed proof of this item. No Lean file was written and no compiler or Lake tool was invoked.

## WANTED

None: all sources needed for this split are present under literature/stacks-project/.

## What needed repair

The imported item had a complete, correct statement but no proof. I supplied the missing argument. I kept its statement, source, statement dependencies, blueprint provenance, created record and all old search entries; there was no earlier sandbox attempt to preserve. There is no repair-note file for this item.

The current latest blueprint direct-images proof (3) was read. The long inherited from.place describes a DAG refinement through alteration inputs; it is not a quotation of the latest proof (3), whose displayed argument is compactification and preservation. This delivery makes no new claim that those alteration details occur verbatim there and changes neither the unit nor chapter route. blueprint_refs.py ancestor returns None, agreeing with the inherited null from.node. The inherited place is already specific and the via chain is retained. Whole-blueprint searches for "universally open", "principal open", "affine fibre product", and "tensor product" found no node equivalent to the present criterion. The last search has many tensor-category hits; those are not this affine geometric statement.

## Unfinished work

None in the stage-1 split. The item is not marked as independently reviewed. Delivery remains subject to the maintainer's independent review.

## Not duplicates

No new node was created. In particular I reused lem-weil-pbc-spec-localization-away-basic-open for the principal-open basis, lem-weil-pbc-open-fibre-product for restriction as an open subscheme, lem-weil-pbc-fibre-product-affine-spectra for the tensor spectrum and both projections, and lem-weil-pbc-affine-opens-basis for the affine cover. I did not make a new affine base-change criterion, tensor-product lemma, open immersion lemma or topological union lemma. The broader chart node lem-weil-pbc-affine-chart-base-change-iso was read but is unnecessary. The ring-fibre-product topology nodes concern Spec of a ring pullback and a topological pushout, a different construction from the tensor product here.

## Mathlib searches and source checks

All new searches used the required msearch.py Q110 lem-sfb-principal-affine-test-universally-open command. Both semantic phrasings, both Loogle patterns, the source grep, and the adaptive grep are preserved verbatim in searches.jsonl and the node. LeanSearch was available for the new query. The hits give definitions and stability/locality of UniversallyOpen, the affine pullback isomorphism, and a descent theorem requiring an additional codescent condition. I read UniversallyOpen.lean lines 35–100, Pullbacks.lean lines 700–780, and Descent.lean lines 85–112. None is a one-line specialization that supplies the entire criterion and its precise identifications. The tensor pullback itself is already covered exactly by the existing Mathlib leaf.

## Review by Q110

I read delivery-errors.md B through E in full against the node and source text. For the item I read Stacks more-morphisms.tex Tag 0F31, label lemma-test-universally-open, the proof of (3) implies (1), including the affine localization paragraph and the principal-open basis paragraph. I also read schemes.tex Tag 01I4 (lemma-fibre-product-affine-schemes), Tag 01JQ (lemma-fibre-product-affines), Tag 01JR (lemma-open-fibre-product), Tag 01IT (lemma-basis-affine-opens), and Tag 01JY (lemma-base-change-immersion), and algebra.tex Tag 00E0 (lemma-Zariski-topology), parts (11) and (14). The tag-to-label mapping was checked in tags/tags. There are no new nodes requiring a separate source review and no SGA source is used.

For step 1 I opened lem-weil-pbc-spec-localization-away-basic-open. Clause (i) explicitly states that the D(g) form a basis for every commutative ring. Applying it to D_B requires no nonzero or finiteness condition. The remainder is the displayed union identity and the hypothesis already on this item. It is elementary relative to that cited statement: every point of V lies in a basic open contained in V, and a point belongs to an image of a union exactly when it belongs to one of the images. I did not cite the unrelated localization/homeomorphism clause (ii) as if it supplied openness of q_B.

For step 2 I opened lem-weil-pbc-open-fibre-product and def-pc-fibre-product. The former explicitly gives the open immersion, its precise image as an intersection of preimages, AND projection compatibility. With the full opens S and X its image is exactly q^{-1}(W). The latter explicitly gives existence, uniqueness and the projection universal property; the proof describes maps in both directions between the iterated pullback P times_T W and X times_S W and checks their composites by the projections. No unsupported assertion that the topological space of a scheme pullback is the set-theoretic fibre product is used. Tag 01JY alone would not have stated the whole image identification; using the exact 01JR node avoids that C4 fault.

For step 3 I opened def-weil-affine-spectrum, def-pc-fibre-product and lem-weil-pbc-fibre-product-affine-spectra. The first states the full ring-map/scheme-map correspondence, not just the definition of Spec. The chosen W-isomorphism therefore gives the required A-algebra structure on B. Swapping factors is justified explicitly by inverse maps and projection uniqueness, so the tensor order is B tensor_A C, as in the item, rather than C tensor_A B silently identified. The affine fibre-product statement gives BOTH projection formulas; with its first algebra B, its first projection is the spectrum of b maps to b tensor 1, exactly q_B. None of the cited statements assumes finite presentation, flatness, nonemptiness or separation. The unique-identification argument is included in this step, not taken from a proof hidden behind a cited statement.

For step 4 I opened lem-weil-pbc-affine-opens-basis, whose neighbourhood form implies that all affine opens cover every T. The image identity is proved by an explicit witness x with q(x)=w; it is not a general base-change image theorem with unstated surjectivity requirements. An open of the restricted source has open image by step 1 and the actual scheme isomorphisms of steps 2–3. An open subset of an open W is open in T, and the union of these intersections is exactly q(O). These are elementary topological and set arguments, with the basis result cited. No finite subcover, affine intersection, noetherian approximation, separatedness or quasi-compactness is used.

B1–B10: no new statement-only nodes, unspecified objects, undefined new notions, unrun recorded searches, invented Mathlib matches or duplicate nodes arise; all new text is TeX encoded once in JSON; the statement and provenance are retained. C1–C8: every non-elementary input is an existing cited statement, read as above; citations.json copies the relevant nodes' actual statement text; all proof dependencies are Mathlib leaves and the universal-property definition, so no dependency on this item or its parent is introduced and no off-unit route replacement is made. D1–D5: the argument itself is in these four steps, not relabelled as a new node, and all source abbreviations needed here (affine localization, principal opens and gluing) are expanded. E1–E7: I checked the hypotheses and object/projection orders in every application; no source error or false item was found and no statement correction is needed.

Small cases checked: g=0 gives an empty principal open, g=1 gives the whole affine source, and arbitrary empty V is the empty union. If B or C is the zero ring then D_B is zero and its spectrum is empty, so its image is empty; the tensor spectrum formula also permits zero rings. The A=0 case forces its unital algebras to be zero. Empty W and T make the same formulas valid. A= C and phi the identity give q_B the identity up to the tensor isomorphism, consistent with all claims. Infinite affine covers and non-quasi-separated T cause no problem because the argument never intersects two affine opens or takes a finite subcover. Every proof step is under 2000 characters; none hides a separate comparison lemma or omitted standard argument.

The Lean skill was used only for its search-before-prove and source-inspection guidance. The explicit stage-1 user rules override compilation workflows. All writes made directly by this worker are confined to the assigned sandbox; the mandatory delivery command manages its own authorized worktree.

# Worker report: lem-a1-space-point-open-calculus

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-point-open-calculus.json: statement, split in seven steps, not a Mathlib leaf. Existing statement and stmt_deps retained verbatim. No new nodes; zero new Mathlib leaves.
- citations.json: seventeen step/cited-node pairs, each quoting the cited statement verbatim. Full statements are retained where the step needs multiple clauses.
- searches.jsonl and search-item-*.txt: actual msearch command records and unabridged returned hits for this item. write_split.py is sandbox-only preparation, not delivery content.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, AlgebraicSpace, algebraic space, points-cartesian and open-subspace notions. No declaration states the item. Scheme-only declarations cannot attach this algebraic-space statement. Existing Sheaf definitions were read for consistency, never edited or compiled.

## WANTED

None. All sources used are present in literature/stacks-project. No SGA source is used.

## Findings and changes

The item was unsplit, with no prior sandbox node, split, report or search log. No stage-1 repair note for it was found. Copied the live item and retained its existing citations, searches, blueprint ancestry, metadata and statement. Added only proof, proof_deps, proof_origin, split_report, split status and the actual new item searches.

Read spaces-properties.tex Tags 03BV (lemma-scheme-points), 03H4 (lemma-points-cartesian), 03H5 (lemma-characterize-surjective), 03BX (lemma-topology-points), 03BZ (lemma-open-subspaces), 03IR (lemma-etale-open) and 03IE (lemma-factor-through-open-subspace). Also read schemes.tex, the field-spectrum discussion preceding 01J9 (lemma-characterize-points), and morphisms.tex 02GN (lemma-composition-etale), 02GP (lemma-open-immersion-etale). Checked tag/label mappings directly in tags/tags.

The 03H5 statement in this source is for a scheme source. Its exact argument extends to the representable source in our item: a field base change is a scheme, and the converse uses the already proved general compatible-pair lifting. The source's second paragraph accidentally writes Z×_X T -> T while immediately explaining that the map to Z must be surjective. Our proof explicitly uses the projection to the base-change scheme and does not reproduce that typo. The item itself requires no statement correction.

The open-subspace inclusion proof does not cite 03BZ as a black-box bijection or introduce an equivalent new clause. It tests each section b in J_1(T): the open subscheme T×_B J_2 has every point, hence is all of T with its restricted structure sheaf. This yields a genuine lift in J_2(T), not an inference that a general immersion factors from image containment. Only open immersions are used here.

Read the chapter/unit records, the three-level rule in SETUP, and the current main-20261015 ancestor lem-a1-affine-hc0 proof. This is the existing auxiliary 03XX/03XW representability branch under that ancestor, not a replacement of the Rankin–Selberg argument. Kept its existing from.node/place/via and searched same_as with blueprint_refs search 'algebraic space points', 'points', '03BX', '03BZ', and 'point classes'; no equivalent imported blueprint statement found.

## Not duplicates

No new nodes. Opened the same-tag neighbors lem-a1-space-fibre-product-point, lem-a1-space-atlas-point-comparison, lem-a1-space-atlas-test-open-subsets, lem-a1-space-affine-etale-cover, lem-a1-space-invariant-open-quotient, lem-a1-etale-atlas-presentation, lem-a1-space-open-factor-scheme-tests and lem-a1-etale-scheme-map-open-image. The existing scheme-atlas theorem is sufficient for the topology input, so neither a new continuity theorem nor a new etale-openness theorem was created. The etale-scheme-map open-image theorem depends on lem-a1-space-etale-open-image, which depends on our item: it was deliberately not cited. The same applies to using the parent open-image theorem itself. Read each actual proof dependency statement and traversed its stmt_deps/proof_deps closure: none reaches this item.

## Mathlib searches

The inherited five 2026-10-22 searches are preserved as source material. This worker also ran the mandated leanfinder, loogle, source grep and leansearch commands through msearch.py; all services answered. Ran a second semantic phrasing for open subfunctors and point-image containment before concluding no match. The returned compatible-pullback declarations are for schemes (Scheme.Pullback.forget_comparison_surjective and Scheme.pullbackComparison_forget_surjective). The returned open-immersion and restriction declarations also concern schemes or general topological/ringed spaces. None gives the algebraic-space point quotient or the relation with open subfunctors. The logged grep AlgebraicSpace|points_cartesian|OpenSubspace returned zero hits. No claim of an unrun search is recorded, and no search result is used as an uncited proof fact. The pre-existing Mathlib leaves lem-weil-pbc-morphism-from-spec-field, lem-weil-pbc-etale-composition-cancellation and def-weil-open-immersion are used through their existing DAG statements.

## Review by Q33

I read delivery-errors B–E in full, including the repeated sections, then reviewed the written steps against the actual node statements and the sources listed above. I signed off on the following specific uses and hypotheses.

Step 1 uses lem-weil-pbc-morphism-from-spec-field for its explicit factorization through the residue-field representative and def-a1-algebraic-space-point-classes for exactly the common-extension relation and scheme point map. The two implications showing a bijection are written out. Equal field representatives cannot change their image scheme point. This supplies the scheme-points identification needed later rather than assuming it silently.

Step 2 uses the common-field equivalence from def-a1-algebraic-space-point-classes, not merely an assertion about fully faithful Yoneda, and the first clause of lem-trf-space-fibre-products-etale-covers for the sheaf fibre product. A field section of that fibre product is exactly a compatible pair of sections; its class proves the required lifting. Projection onto the second coordinate then gives the inverse-image/image identity. This is a direct universal-property argument, so it is elementary. No claim of bijectivity is made: different field-valued points can lie above the same pair.

Step 3 uses def-trf-algebraic-space for representability and the definition of surjectivity on every scheme test, plus the residue-field representative explicitly supplied by lem-weil-pbc-morphism-from-spec-field. It does not infer lifting to the original field: the lift is over the residue field of a point of the nonempty field base change. In the converse, both spaces really are schemes by representability; step 1 therefore justifies ordinary surjectivity from the point-class assertion of step 2. This is the elementary application of the preceding steps and the definitions, not an unproved base-change theorem.

Step 4 uses the exact concluding clauses of lem-a1-space-affine-etale-cover: atlas independence, continuity of all scheme-source maps, and openness for representable etale scheme-source maps. It compares the quotient topology with def-a1-space-point-topology's final topology explicitly, since the existing node mentions the former. The arbitrary morphism a need not be representable or etale: the composite with an etale scheme test is a scheme-source map, for which the cited statement gives continuity. The inverse-image equality proves continuity in the final topology. This is marked non-elementary because it uses the established atlas theorem.

Step 5 again uses the atlas theorem, its surjectivity on point classes, and its scheme-source openness clause. It does not assume that a composite with an atlas is etale without justification. The two successive pullback schemes are displayed, and def-trf-algebraic-space makes their projections etale. Clause (2) of the Mathlib leaf lem-weil-pbc-etale-composition-cancellation makes their composite etale. Thus the composite scheme-source map has exactly the representability and etaleness required for the openness theorem. The displayed image equality uses surjectivity of the chosen atlas. There is no quasi-compactness, separatedness, finite-type or base-affineness hypothesis.

Step 6 uses def-a1-space-open-subspace for both the subfunctor injection and the scheme-test open immersions; clause (1) of lem-weil-pbc-etale-composition-cancellation makes them etale. Subfunctor injectivity is used after restricting both representatives to the same field, as required by def-a1-algebraic-space-point-classes. The continuous/open map is therefore an injection and its inverse onto the image is continuous because open sets have open images. This is elementary after steps 4–5. The atlas inverse-image assertion is step 2, with the scheme/open-immersion interpretation supplied by step 1 and def-weil-open-immersion. It holds for every scheme atlas, not just the particular affine-refined atlas used earlier.

Step 7 uses def-a1-space-open-subspace only for an actual open scheme test. A section of J_1 over T forces every residue-field class into J_2; step 2 therefore gives full point image of the open subscheme P. The cited def-weil-open-immersion explicitly identifies an open immersion with the restriction to its image including its structure sheaf, so full image gives an isomorphism, not just a bijection. Its inverse gives the required lift of the original T-section. This proves subfunctor containment on every scheme and hence the final equality assertion. No descent theorem, factorization theorem for general immersions, or proof of a neighboring node is being borrowed.

Checked the empty algebraic space, empty source, empty open subspace, identity atlas of a scheme, full open subspace, non-surjective etale maps, two unrelated field representatives requiring a common extension, and arbitrary nonrepresentable morphisms in the first and continuity clauses. Empty A gives empty fibre product and empty image; empty B permits only empty sources. An empty atlas is used only for the empty target. Full image of an open immersion retains the full structure sheaf, excluding the false closed-immersion analogue. Every morphism and common field extension respects the base S by the point-class definition. All seven proof steps are shorter than 2000 characters; none hides a comparison lemma. No new statement requires separate edge-case review.

The only non-Mathlib off-unit statement cited is lem-trf-space-fibre-products-etale-covers. Its first clause is an algebraic-space existence/universal-property tool, with no invocation of the trace formula or Poincare duality; it is declared in split_report.tool_uses. Its dependency closure was checked for cycles. Its second covering-family clause is not used. The other off-unit inputs are definitions or existing Mathlib leaves. Citation quotes were generated from the exact statements just reviewed, one for every use.

## Unfinished work

No mathematical part left open in this split. The existing unsplit dependencies remain their own items. Server mechanical dry run and delivery are performed after this report is written; command output supplies the delivery status.

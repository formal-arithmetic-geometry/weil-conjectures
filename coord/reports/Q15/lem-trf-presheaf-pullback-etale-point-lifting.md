# Stage-1 report: lem-trf-presheaf-pullback-etale-point-lifting

## Files written

- dag/nodes/sec-trace-formula/lem-trf-presheaf-pullback-etale-point-lifting.json: item, status split; unchanged statement, five explicit elementary proof steps. Mathlib searches found component tools but no match for the whole assertion.
- citations.json: one verbatim statement quote for every step/node citation.
- searches.jsonl: actual Mathlib search log, retained verbatim.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean written and no compiler, Lake, build or local DAG/preflight check run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for algebraic-space, representable-etale and field-point language. No project declaration states all the item. The related side-library declarations AlgebraicGeometry.AlgebraicSpace.etaleCover_pullback and etale_fibreProduct_isScheme in lean/Sheaf/AlgebraicGeometry/AlgebraicSpaceFibreProductsEtaleCovers.lean (77, 95) have sorry proofs (85, 99), so are not attachments; moreover their hypotheses restrict to algebraic spaces, whereas this item works with arbitrary sheaves. Read the actual point-lifting definition in AlgebraicSpaceJointSurjectivity.lean, which agrees with the cited definition node.

## WANTED

None. The necessary literature is available locally. No SGA source is used.

## Corrections and scope

The imported statement is correct and is preserved verbatim. Its proof was empty. The source Tag 041F(3) has an omitted proof, so proof_origin.by is agent: this delivery supplies those details rather than claiming an existing source proves the arbitrary-sheaf formulation verbatim. The argument of Tag 03H4 is applicable as a model for constructing a compatible pair, not as a theorem cited beyond its algebraic-space hypotheses.

No extra common-field lemma is needed: the statement of def-trf-algebraic-space-jointly-surjective-family already gives an extension of the given K and a representative over that extension. No theorem identifying scheme points with presheaf point classes is used. No theorem asserting etale stability under scheme base change is needed either: the scheme-test identification yields literally the same representing scheme over T as in the hypothesis. The five elementary steps write out all required manipulations, rather than creating nodes for clauses of this item.

Read dag/chapters/sec-trace-formula.json and dag/units/sk-i-curve-zero.json. This is a historical polarized-descent helper in the existing from/via chain, inherited from old steps 6,7 of lem-trf-space-fibre-products-etale-covers; it does not change the chapter or replace the unit's contracting-correspondence route. Read the current ancestor's statement/update to distinguish that route from the historical helper. No unit realization is changed because this is not its key statement.

## Unfinished work

None in the one-level stage-1 split. Proving declarations in Lean is outside this dispatch.

## Not duplicates

No new nodes, so no new/existing pairs require separation. Whole-DAG searches for 041F, 03BU, 03H4, common-field and joint-surjectivity language located the existing definition, the parent fibre-products node, lem-trf-sheaf-pullback-diagonal, lem-a1-space-fibre-product-point and lem-trf-family-common-extension-field. Read their statements: the diagonal node assumes representable diagonals, the point lemma assumes an algebraic-space target and scheme factors, and the common-extension lemma constructs fields rather than the required compatible sections. None replaces this arbitrary-sheaf assertion or is needed as an additional dependency. Blueprint search for 'representable etale', 'point classes', and 'scheme tests' had no matching imported nodes; 'field extension' and 'pullback' exposed general field/scheme/derived results, not a second copy of this claim. same_as remains [].

## Mathlib search results

Ran and read all five searches recorded in searches.jsonl: LeanSearch, Loogle, grep and two LeanFinder phrasings. Retained the item's inherited searches as prior research and added these actual Q15 searches. All current services answered. Loogle returned generic relative representability and its base-change theorem; read Mathlib/CategoryTheory/MorphismProperty/Representable.lean, including the definition and API. Read the Zariski local-representability context in Mathlib/AlgebraicGeometry/Sites/Representability.lean. LeanSearch also returned scheme etale permanence and scheme jointly-surjective precoverage; LeanFinder returned scheme pullback maps. These do not state the full item, especially the field-extension lift condition for arbitrary scheme presheaves, so this is not a Mathlib leaf. The item is proved directly with definitions, not by treating unrelated matches as exact results.

## Review by Q15

I read spaces-topologies.tex Tag 041F (lemma-etale), including the explicit 'Omitted' proof, spaces.tex definition-relative-representable-property (the scheme-test convention), and spaces-properties.tex Tag 03BU (definition-points) with the preceding presheaf equivalence definition and Tag 03H4 (lemma-points-cartesian) with its common-field proof. I checked the tag/label mapping in tags/tags. Those sources explain both the intended cover pullback and the field-extension construction. There are no new nodes to source or review.

Step 1 cites def-weil-pbc-sites-and-cohomology for exactly its equalizer definition of a sheaf and the full-subcategory convention. I read that statement, not its proof. The step glues each component using G and H_i and invokes uniqueness in H to establish the defining equality; this works for every covering, including an empty covering. The projection and universal property are specified componentwise, so no uncited limits theorem is hidden.

Step 2 cites that same sheaf definition for viewing the pointwise objects as sheaf products via Step 1. Its two displayed formulas give inverse transformations: the left equality t_U(a)=x is exactly the equality discarded and recovered by the inverse. I checked the restriction formula t_V(a composed with b)=t_U(a)|_V, which establishes naturality; both maps preserve a and thus the projection to T. It uses no Yoneda identification theorem: t is already a natural transformation in the statement, and h_T(U) is explicitly Mor_S(U,T).

Step 3 cites def-trf-algebraic-space for its actual scheme-test definition of representable etale maps, not for an unstated base-change theorem. I read that node and checked that g composed with t has the required target H, and that the representing scheme from h_i has the same projection to T under the preceding explicit isomorphism. For G=h_T, the identity test and the displayed inverse p maps to (pi_i(p),p) prove the scheme clause. Nothing requires G, H, or H_i to be algebraic spaces, to have representable diagonals, or to admit atlases.

Step 4 cites def-trf-algebraic-space-jointly-surjective-family for its full quantified extension-lift condition. I read the statement and verified that its input is g_K(x), rather than x in the wrong presheaf. It gives exactly the index, embedding and section over s composed with Spec(e) required here. Naturality of g proves compatibility, so the ordered pair lies in P_i and its first projection is x restricted to M. The same definition supplies the final point-class interpretation. No separable, finite, algebraic or algebraically closed extension is assumed.

Step 5 cites the same quantified condition and applies it to g_K(x) to derive an impossible index when I is empty. I checked the empty base and empty sheaf cases: without any field-valued x the lifting quantifier is vacuous, and the componentwise scheme-test arguments remain valid. For a nonempty simple example, take g and the single h_i to be identities: the formulas reduce to inverse coordinate deletions and insertions and the lift can use M=K. These tests support every clause without adding hypotheses.

I checked delivery-errors B through E against the files: no new statements lacking notions, no source section substituted for a tag, no duplicate nodes, no implicit non-elementary assertion, no use of a cited proof in place of its statement, and no re-labelled subclause. All step citations are definition statements that say exactly what is used, with verbatim excerpts in citations.json. The item statement is unchanged and each step is below 800 characters, so no >2000-character step hides a lemma. All steps are elementary because the gluing, inverse maps, and quantified witnesses are actually written out; none simply asserts the whole result from a definition.

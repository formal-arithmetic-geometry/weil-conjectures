# Stage-1 delivery: lem-sfb-fpqc-labelled-clopen-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fpqc-labelled-clopen-descent.json: existing statement, now split in four steps; no exact Mathlib match.
- citations.json: verbatim statement excerpts for all seven step/node citations.
- report.md: this report. searches.jsonl is the search tool's unmodified log.

New nodes: 0. New Mathlib leaves: 0. The existing statement, statement dependencies, source, creation record, blueprint provenance and earlier searches are retained.

## Attachments

None. Searches of lean/WeilConjectures/ for the item id, its blueprint tag and fpqc/label/clopen terminology found no declaration stating the whole item. The completed AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc in AlgebraicGeometry/FpqcOpenSubschemeDescent.lean:51 proves compatible-open descent, not the full labelled partition and test comparison; it already belongs to lem-weil-pbc-open-subscheme-fpqc-descent and is used through that node.

## Wanted sources

None. No WANTED request is needed.

## What was wrong and what changed

The item was statement-only with no proof. Its statement is true and is unchanged. The current blueprint rank proof explicitly follows fpqc descent of opens; this split follows that route. Rather than add new nodes restating the partition or its comparison clause, the item itself carries the elementary pointwise arguments. The two non-elementary inputs already exist: compatible-open descent (03N0) and fpqc base change (022D(3)). No unit or chapter record is edited; this item is not its unit's key statement.

The generic off-unit tool lem-weil-pbc-open-subscheme-fpqc-descent is declared in split_report.tool_uses: the unit explicitly needs that theorem, but does not itself state it. The base-change node and all cited definitions are existing Mathlib leaves. No maintainer-owned tool_uses field is changed.

## Searches and nonduplication

Read the earlier Q125 item searches and their results. Ran eight additional searches with the required msearch.py command, using two phrasings across LeanFinder, LeanSearch, Loogle and Mathlib grep; their exact queries and tool result records are appended to mathlib_searches and remain in searches.jsonl. All services returned successfully. The search hits are not exact matches: FlatDescent.lean:133 descends the property of being an open immersion along a single surjective flat quasi-compact morphism; Topology/Clopen.lean:136 reflects clopenness when a quotient map is already supplied; LocallyConstant/Basic.lean:424 reflects local constancy through an injective map of codomains, rather than descending functions on scheme covers. The semantic hits about affine transition limits or profinite inverse limits impose different objects and hypotheses.

Searched the whole DAG by 03N0, 022D and fpqc/clopen/label keywords, and searched blueprint_refs.py with fpqc, clopen and fpqc labelled clopen descent. There is no blueprint node stating this item in another form, so same_as stays empty. The general compatible-open node is reused. The etale-open-fpqc-descent node additionally assumes an etale test scheme and only descends one open, so is unnecessary. No new node is created, and no new-node/existing-node duplicate pair arises.

## Review by Q158

I read the item against Stacks descent.tex, Tag 03N0 (lemma-open-fpqc-covering), including its proof, and topologies.tex, Tag 022D (lemma-fpqc), especially part (3). I also read the current main-20261015 rank proof, the sk-lem-stratified-lattice unit and the six-functor chapter, keeping the rank paragraph's route. The proof_origin is marked agent because the label-by-label assembly and test comparison are written out here using these source lemmas. There are no new nodes requiring separate source review.

Step 1 uses def-weil-open-immersion only to give each open fibre its restricted structure sheaf, and lem-weil-pbc-open-subscheme-fpqc-descent for existence of the descended open. I opened both statements: the latter supplies descent for an arbitrary fpqc covering family with equality of inverse images on every double fibre product. Equality of the two label functions gives exactly that hypothesis by evaluating membership at a point. No clopenness or finite number of labels is required to apply this input.

Step 2 uses def-weil-pbc-fpqc-covering, whose statement explicitly gives joint surjectivity. A lift u of any x makes membership in Z_a equivalent to the single equation rho_i(u)=a. This proves the partition and uniqueness directly, and makes each complement the union of all differently labelled open pieces. This is an elementary set argument from Step 1, not another descent lemma. Arbitrary unions are open, so no finite-label restriction enters.

Step 3 uses lem-galois-fpqc-covering-base-change: its statement allows any base morphism and arbitrary covering index set. It writes the factors in the opposite order, so I cite def-pc-fibre-product and use the canonical exchange isomorphism from its universal property. The projections in the item are thus exactly a base-changed fpqc cover. The fpqc definition supplies joint surjectivity, with no quasi-compactness of V or X.

Step 4 again cites the definition's joint-surjectivity clause. For each v, the lifted w in the scheme fibre product gives h(v)=f_i(q_i(w)); the already proved inverse-image identity and the given test compatibility supply the displayed chain of membership equivalences. This does not assume that points of a scheme fibre product are pairs of topological points. The point w is obtained from the base-changed cover, so no unstated fibre-product-points theorem is used. Continuity of a scheme morphism then gives the final open-and-closed assertion.

I checked delivery-errors B through E against these steps. Every cited node was opened and every quote in citations.json checked literally against its statement. No non-elementary fact is left as an uncited tag; no node's proof is used as if it were its statement. No new statement-only nodes, duplicates, or relabelled item clauses are introduced. The proof has four steps of 514, 635, 391 and 530 characters, all below the long-step review threshold. The two elementary steps are membership arguments from the previously established opens and covering property.

For small cases: if I is empty, the covering definition forces X empty, and a map V to X forces V empty. If A is empty, the functions rho_i force every U_i empty and joint surjectivity forces X empty; the empty partition is unique. Empty X, empty test V, empty individual U_i and singleton A satisfy the same argument. Infinite I and A, non-quasi-compact X, and sigma not initially locally constant cause no extra restriction: base-changed joint surjectivity proves its fibres are exactly inverse images of the descended clopen subsets. No source or statement dispute was found.

## Unfinished work

None for the authorized stage-1 split. Delivery is subject to the required server dry run and independent maintainer review.

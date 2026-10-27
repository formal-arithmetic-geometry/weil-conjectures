# Q116 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibred-groupoid-representable-smooth-calculus.json: statement, split, no Mathlib match. Seven proof steps; no new nodes and no new Mathlib leaves.
- citations.json: one verbatim dependency statement per step/node pair (24 pairs).
- searches.jsonl and search-1.txt through search-5.txt: actual Q116 search records and their full outputs. write_split.py is sandbox-only preparation material.

## Attachments

None. Searching WeilConjectures for the exact blueprint tag and fibred-groupoid/representable-smooth terminology found no project declaration giving this item. General representability and scheme smoothness hits are not attachments.

## WANTED

None for the mathematics. The inherited brief mentions coord/dag-sync.md, which is absent in the shared repository; its old isolated-clone instructions are superseded by this direct-delivery brief.

## Corrections and scope

The statement and its seven statement dependencies are unchanged. The imported source gave statements with formal/omitted proofs, not an already completed split. I expanded their arguments using existing nodes rather than creating clause copies. In particular I did not apply the existing stack-chartwise calculus to non-stacks: that node assumes algebraic stacks, a hypothesis this item explicitly excludes.

The inherited blueprint ancestry has no machine-resolvable ancestor; blueprint_refs.py ancestor reports None. Searches of all imported blueprint nodes for representable smooth, fibred groupoids, 0300, and etale calculus found no equivalent blueprint statement. I read the latest blueprint (COMMITS.txt main-20261023-1620): sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. Its paragraph (3) now delegates open direct images to the appropriate constructibility results; the long inherited alteration/moduli ancestry is historical, not the current paragraph's verbatim argument. This split is the generic calculus prerequisite for the existing algebraic-stack fibre-product construction (Stacks 04TF), below that inherited route; it neither changes a unit nor chooses a replacement direct-image route.

## Not duplicates

No new nodes. Existing lem-sfb-representable-pullback-over-space is used for Tag 0300. Existing lem-sfb-space-etale-presentation-property-criterion and lem-sfb-scheme-etale-source-target-properties provide the chart criterion, and existing algebraic-space fibre-product/chart nodes provide chart permanence. The stack-chartwise calculus has stronger stack hypotheses, so it cannot close this item by itself. New nodes duplicating these inputs or restating the item's clauses were deliberately avoided.

## Review by Q116

I read algebraic.tex, lemma-base-change-representable-by-spaces (0302), lemma-base-change-by-space-representable-by-space (0300), lemma-composition-representable-by-spaces (0301), lemma-map-presheaves-representable-by-spaces-transformation-property (045A), and lemma-composition/base-change-representable-transformations-property (045B/045C). Their hypotheses are categories fibred in groupoids, not algebraic stacks. I also read spaces-morphisms.tex lemma-local-source-target (03MJ), remark-composition-P, the smooth definition and composition/base-change lemmas (03ZD/03ZE), and etale-smooth (04XX); and spaces-properties.tex definition-etale, etale-local (03FS), composition-etale (03FT), base-change-etale (03FU). Tags were checked against tags/tags. No SGA source is used. There are no new statement-only nodes whose source would need a separate review.

Step 1 uses exactly the fibrewise triple and arrow formulas in def-sfb-stable-pointed-moduli-groupoids. I wrote the equivalence and its inverse, including the natural isomorphism and restriction compatibility; all four base-change conclusions then reuse literally the same scheme tests. This is a formal elementary argument, not an appeal to a property-descent theorem.

Step 2 uses that definition and the full statement of lem-sfb-representable-pullback-over-space, which permits arbitrary fibred groupoids and an arbitrary algebraic space source Z. Its hypotheses hold with Z=B because the second morphism is representable. The explicit equivalence with the composite's test supplies the omitted detail of 0301. It uses neither the proof of the cited node nor the theorem currently being split.

Step 3 uses both locality nodes: the scheme node certifies smooth/etale source-and-target locality, and the presentation criterion actually supplies P(U->V), P(V->T), and finally P(A->T). The chart-existence hypotheses come from def-trf-algebraic-space; the fibre-product/etale-cover node supplies E->A, and representable-etale-scheme-tests supplies composition of its chart with U->E. Scheme composition is precisely the statement of lem-trf-smooth-composition or clause (2) of lem-weil-pbc-etale-composition-cancellation. I checked that U and V are schemes, A and B algebraic spaces, and T a scheme. No chart of F, G or K occurs. Every non-elementary input is a named existing node, not a tag-only citation.

Step 4 cites the actual field-extension lifting definition and the groupoid triples. Given t, it first lifts along g after K->L and then along the scheme test of f after L->M. The isomorphism returned by that test is exactly the third component required for A, so it gives a lift after the composite field extension. This is a direct elementary manipulation of the two definitions. It does not incorrectly assume lifting over K itself or effectivity of descent.

Step 5 uses the presentation/locality nodes for etale and smooth separately, and only the etale-implies-smooth clause of lem-weil-pbc-etale-smooth-zero-dimensional-fibres. I checked its source/target are the scheme charts U and V; I do not take a conclusion about algebraic spaces directly from that scheme lemma.

Step 6 cites algebraic-space fibre products to construct the tests of G->F, the triple definition to identify these discrete-groupoid tests with ordinary sheaf fibre products, and the presentation/locality statements for the scheme comparison. Scheme representability is an additional hypothesis only for the comparison clause, not for all maps of algebraic spaces.

Step 7 cites the actual scheme-surjectivity definition, scheme surjectivity under arbitrary base change, residue fields, and the algebraic-space definition. These statements justify choosing a residue field of a point of W_K and conversely testing Spec kappa(t). This supplies the topological-versus-field-lifting comparison rather than silently equating the definitions. The chart case has scheme representability by the algebraic-space definition.

I checked B--E against these steps: no new-node shape issue, no hidden non-elementary uncited input, no citation to a proof-only construction, no cycles intended, no hypothesis added to the item, and no relabelled clause nodes. All step lengths are below 1000 characters, so none triggers the 2000-character long-step inspection. Small cases checked: empty test schemes, empty spaces, identities, a nonempty source over a field whose point only exists over an extension, and arbitrary non-stack base-changing groupoids. The point argument correctly uses extensions and the empty-target cases are vacuous. The three generic off-unit tools are declared in split_report.tool_uses with their precise roles; no top-level tool_uses field was set.

Mathlib searches used the required msearch.py command only. I read all hits and ran a second semantic phrasing. Mathlib's relative representability definition is for ordinary categorical pullbacks; there is no one-line specialization to the algebraic-space groupoid 2-pullbacks here. I read the relevant definition in Mathlib/CategoryTheory/MorphismProperty/Representable.lean and the scheme smooth/etale source. Existing inherited N9 search records are retained, and the five real Q116 records are appended. No unavailable service was recorded as a negative result.

## Unfinished work

None in this one-level split. Existing dependency nodes remain their own items. No Lean was written and no compiler, Lake, or local DAG/preflight check was invoked.

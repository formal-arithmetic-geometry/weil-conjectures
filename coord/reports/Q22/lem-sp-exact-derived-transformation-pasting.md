## Worker report

Q22 split lem-sp-exact-derived-transformation-pasting in nine steps, with zero new nodes and zero new Mathlib leaves. The mathematical statement is unchanged. Its statement dependencies now explicitly include lem-sfb-exact-derived-composition, which supplies the standard comparison already mentioned in the statement. The proof uses existing exact-factorization, ordinary-derived-category, localization-universal-property, and normalized-compositor nodes. No dependency was removed. No Lean was written or compiled.

The proof normalizes every derived transformation by a_P:T_P Q -> Q C(P), where T_P is the word of the chosen derived edge functors. It proves both whiskering formulas, including naturality at the derived factorization morphism for input whiskering. Cancellation of a_R and localization extensionality then descend each equation. It never cancels an ordinary cell and therefore applies to noninvertible cells. The comparator direction is checked explicitly: mu:D(GF)->D(G)D(F), so t^D=mu_target D(t) mu_source^{-1}.

## Sources and searches

I read derived.tex Tag 015F, label lemma-right-derived-exact-functor, statement and proof (lines 5883-5903); categories.tex Tag 04VG, label lemma-properties-left-localization (lines 4405-4430); and Mathlib/CategoryTheory/Localization/Predicate.lean:278-361. The Stacks functor universal property by itself does not state the fully faithful natural-transformation enhancement. The existing localization-universal-property Mathlib leaf does, and its statement was read in full. The pasting argument is therefore marked agent-written, not attributed wholesale to Stacks.

I read the current blueprint det-sp-tower-gluing statement and its proof's Local pairs context, the chapter and sk-prop-sp-tower-geometric unit records, and the parent lem-sp-varying-ring-proper-open-pasting. This item supplies the descent from the ordinary proper/open identities to actual derived transformations. It neither replaces the tower-geometric route nor uses SGA.

Project searches for the exact blueprint tag, liftNatTrans, mapDerivedCategory transformations, and derived pasting found no declaration giving the whole item. I read MapDerivedCategoryCocycle.lean and the derived-square pasting candidates: those treat invertible cells or particular square geometries. They cannot be attached for this arbitrary noninvertible-cell item. The DAG searches found lem-pod-derived-exact-square-composition and lem-weil-pbc-derived-square-pasting, again for invertible cells. I reused the strictly smaller existing generic nodes rather than introducing a new statement of a clause of the item.

The whole-blueprint searches were `tools/blueprint_refs.py search 'localization'`, `'natural transformations'`, `'exact derived'`, `'localization preserves'`, and `'exact functor'`, with the ancestor command confirming det-sp-tower-gluing. No imported blueprint node states the full arbitrary-cell assertion; blueprint.same_as remains []. The pre-existing from.place identifies Local pairs and is already specific.

All five new Mathlib searches were run using the required msearch.py command and their actual results are in searches.jsonl. Both leanfinder phrasings, leansearch, loogle and grep returned successfully. I read the liftNatTrans, liftNatTrans_app, comp_liftNatTrans, liftNatTrans_id and natTrans_ext hits. These give the local lifting/vertical-composition statements already carried by the existing localization leaf, not the entire comparison-normalized exact-derived horizontal-pasting assertion in one line. The general left/right derived transformation hits likewise do not give the whole assertion. Earlier search records in the imported item were preserved verbatim.

## New nodes

None. There are no new unsplit statements, definition nodes, or Mathlib matches to validate. No unit realization record changes are needed: this is not the key node of the unit.

## Not duplicates

No new nodes. In particular the proof cites lem-sfb-exact-derived-composition rather than making another compositor node. The existing invertible square-pasting nodes do not cover noninvertible cells and were not used as substitutes.

## Review by Q22

I checked the proof against the actual statements in the four cited node files, not their proofs. The quote for every use is copied verbatim into citations.json. Reading 015F confirmed that unbounded complexes are allowed and exactness supplies quasi-isomorphism preservation. Reading 04VG confirmed its narrower functor-only scope; this is why the proof also explicitly uses the Mathlib localization statement rather than claiming that Stacks states all the pasting laws.

Step 1 uses def-weil-abstract-derived-category only for the definitions of a cochain complex and its morphisms. Naturality at the differential is exactly the required chain-map equation. The componentwise identity/composition/whiskering statements are definitions, so this step is elementary.

Step 2 uses the exact-factorization node for quasi-isomorphism preservation and the natural isomorphism a_F on every complex. All its hypotheses hold for an edge and a composite: the functors are additive and preserve finite limits and finite colimits, with composite preservation obtained by applying them successively. The cited compositor node really states mu:D(GF)->D(G)D(F) and its a-normalization, in that direction. The recursive word factorization is a composite of those isomorphisms. This is a non-elementary step because it invokes exact descent.

Step 3 uses the derived-category definition for Q being a localization. Clause (2) of the localization-universal-property node really permits arbitrary natural transformations, with any chosen lifts and their lifting isomorphisms; it is not restricted to invertible cells. Taking the target category to be D(B) has the required chosen category/universe. The word functors invert quasi-isomorphisms by Step 2. The compositor node's actual displayed equation verifies the conjugation formula, with inverse source mu and forward target mu. This second non-elementary step constructs the cell, rather than delegating the pasting assertion to a new lemma.

Step 4's two cancellations use only the invertible lifting isomorphisms. Clause (3) of the cited localization node states precisely the equality test at all QK. Its use is about natural transformations of functors out of D(A); it does not assert that Q is faithful on arbitrary morphisms. The remaining identity and vertical-composition calculation is elementary.

Step 5 explicitly applies naturality of a_V to the complex morphism C(t)_K, and gives each line of the output-whiskering calculation. Step 6 explicitly applies naturality of t^D to a_U,K, a morphism in the derived category, then substitutes the normalization at the complex C(U)K. Both steps use the equality clause of the localization node only after obtaining the component equation. Their additional algebra is elementary; no faithfulness of evaluation and no ability to lift a_U,K to a complex map is assumed.

Step 7 uses clauses (2) and (3) of the localization node for the uniquely normalized identity lift and its invertibility, and the compositor node for the two-edge normalization. I checked the three-edge paths l and r separately: the right path requires naturality of mu_G,H at a_F,K. I expanded that calculation in the delivered text, instead of leaving a bare coherence claim. The word-length induction has length-one base, append-one-edge step, and separate empty-word normalization giving the unit comparison D(1)->1. These are the same few-line naturality/cancellation argument applied repeatedly, not a new non-elementary coherence lemma. No proof step is over 2000 characters.

Step 8 states the induction on finite expressions, its generators, and each constructor case already computed in Steps 4-6. Once normalized, equal ordinary expressions give equal complex transformations, so clause (3) applies. A horizontal paste is the composite of the two whiskerings; the other square orientation is another such expression. This elementary induction is the deduction of the claimed pasting equations, not an invocation of a new node restating them.

Step 9 derives invertibility by applying the identity/composition rules to both inverse equations. The exact-factorization node is cited again for the only analytic hypothesis used, exactness and its unbounded factorization. No resolution or boundedness input was smuggled in.

I tested the small cases: zero cells remain zero by conjugating zero components; the zero exact functor and identity functor satisfy the normalization; an empty word uses the separate unit comparison rather than identifying D(1) with 1 by fiat; two zero cells and cells with only one invertible side do not trigger any illegal cancellation; arbitrary unbounded complexes enter only through their degrees and Q. With no new nodes there are no new-statement edge cases to add. The item itself has no statement dispute or extra hypothesis. Every non-elementary input is an existing cited statement, all cited files were opened, and all proof dependencies are exactly the union of uses.

The one off-unit non-Mathlib statement, lem-sfb-exact-derived-composition, is declared in split_report.tool_uses. It is a generic normalized-compositor tool, not a replacement of a step of the tower-geometric unit. The other external statements are existing Mathlib leaves. No maintainer field was edited, and the blueprint ancestry and mathematical statement were preserved.

# Stage-1 delivery: lem-sf-ringed-open-roos-preservation

1. Files written: `dag/nodes/sec-smooth-purity/lem-sf-ringed-open-roos-preservation.json` (statement, split, no Mathlib match); `citations.json`; this report. There are 0 new nodes and 0 new Mathlib leaves. `searches.jsonl` is the search command's unmodified log.
2. Attachments: none. Searches of the project declarations for the exact blueprint tag, Roos preservation, extension by zero and products found no declaration giving all clauses for arbitrary ring sheaves and arbitrary schemes. The finite/condensed coefficient extension modules supply other interfaces, not this theorem.
3. WANTED: none.
4. The imported statement is correct; it is unchanged. It lacked a proof. The old seed searches were retained and five actual logged searches were added. The statement dependency on products was made explicit. The blueprint ancestor and its exact integral-construction place are retained. No unit record is changed: this item is a subsidiary lemma, not the unit's key statement.
5. Nothing mathematical remains unfinished in this split. The dry run and delivery results are recorded by the required tool.

## Sources and searches

I read Bhatt–Scholze Lemmas 6.1.12–6.1.13 and the following remark in the local PDF: the homotopy-limit argument uses the open/closed triangle. I read Stacks proetale.tex Tags 09AA (lemma-closed-immersion), 09AG (lemma-jshriek-zero), 09BN (lemma-open-immersion), 09AH (lemma-ses-associated-to-open), and 09BP (lemma-j-shriek-limits). I also read derived.tex Tags 015F (lemma-right-derived-exact-functor), 0145 (definition-triangulated-category, especially TR1), and 08TC (definition-derived-limit). The canonical Roos equations and the arbitrary-ring refinement are marked as agent-written rather than claimed verbatim from the PDF.

The DAG/blueprint searches found `lem-cbc-ringed-open-extension-products`, which already supplies precisely the sheaf-level comparison including its projections and naturality without qcqs hypotheses on X. It is used, and no new node repeats it. `det-sf-open-closed-extension-zero-limits` covers a derived version only when X is qcqs, so it cannot by itself be applied to this item. `lem-sfb-condensed-open-extension-products` has different coefficients and a qcqs hypothesis and was not substituted for ordinary module sheaves. `det-pe-products-derived` states the needed unbounded derived product computation for arbitrary ring sheaves. These are generic tools, declared in split_report.tool_uses where required.

The five commands logged in searches.jsonl were read as returned. Loogle gave the usual presheaf/sheaf-module forgetful and evaluation limit-preservation instances; I read the sheaf limits file. LeanSearch returned zero-map and square-zero-extension declarations. The first LeanFinder query gave condensed AB4-star and finite-product results; the second gave general triangulated-functor declarations, whose map-distinguished interface I read. None supplies pro-etale ringed extension preserving derived countable products under this item's hypotheses. Grep returned no matches. All services responded successfully. There are no new-node searches to invent or backfill.

## Not duplicates

There are no new nodes. The sheaf product lemma found by the whole-DAG search is cited directly. The item is stronger in scope than the existing qcqs/condensed derived assertions and includes explicit projection and transition normalization.

## Review by NK

I checked delivery-errors B–E against the source text and all cited node statements. No new statement-only node is needed, and no clause of the item has been renamed into a new node. The source locations are named by their Stacks tags and labels rather than changing section numbers. Every node cited in a proof step has its verbatim statement in citations.json.

Step 1 uses exactly `lem-cbc-ringed-open-extension-products`: its statement permits any scheme X, any sheaf R of commutative rings, and any small family, and explicitly identifies the projections and asserts naturality. The restriction R|U is the pure inverse image R_U of the item. Countability is a specialization of the allowed small index set. This is a direct application, marked elementary.

Step 2 uses the exactness clause of `lem-weil-pbc-proetale-ringed-open-closed`, the termwise triangulated functor of `lem-sf-exact-functor-derived-triangulated`, and the full statement of `det-pe-products-derived` on both schemes U and X. The latter allows unbounded complexes of modules over arbitrary ring sheaves and supplies the termwise products and their quasi-isomorphism invariance. The sheaf comparison commutes with differentials by its stated naturality. Its localized projections are J of the original projections; the product universal property in `def-weil-category-product` makes the resulting isomorphism the specified canonical one. No claim that j_! preserves K-injectives is used.

Step 3 uses additivity of the exact derived functor and the coordinate definition in `def-weil-derived-limit`. I wrote out every projection of both composites: both are J(pr_n) minus J(d_n)J(pr_{n+1}). Product uniqueness identifies the maps. The first map likewise has n-th component J(pr_n c)=J(c_n). This calculation takes place in the derived category, so it does not silently assume strict realizations of arbitrary derived transition maps. These are elementary coordinate calculations from the cited statements.

Step 4 uses the triangulated-functor assertion, TR1 as explicitly stated in `def-weil-triangulated-category`, and the definition of a derived limit. It specifies the last arrow as xi J(delta) Phi^{-1}, so there is an actual triangle isomorphism with the image triangle. The preceding coordinate computation gives exactly the required middle and first arrows. No uniqueness or functorial choice of a homotopy limit is asserted.

I tested U=X, U empty, the zero ring sheaf, zero complexes, zero transition maps and identity transitions: the comparison reduces respectively to identity, zero, or the same projection calculation. Empty/zero products in a module category cause no exception. No boundedness, constructibility, Noetherian, constant-ring or qcqs assumption on X is introduced. Quasi-compactness of j is retained wherever the sheaf-product theorem and ringed localization need it. No proof step exceeds 2000 characters or hides a separately quantified comparison lemma. No Lean file, compiler, Lake command, repository file or launcher file was written or run.

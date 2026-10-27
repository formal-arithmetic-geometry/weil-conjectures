# Worker report: lem-sf-finite-immersion-constructibility-interval

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-finite-immersion-constructibility-interval.json`: statement item, now split into seven steps; no Mathlib match for the entire statement.
- `citations.json`: 19 entries, one verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. The item statement, statement dependencies, provenance, and imported/maintainer fields are unchanged. No unit realization record is changed: this item is a supporting lemma, not the unit's key node. No Lean was written and no compiler, Lake, or build command was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and the immersion/constructibility/interval notions. The tag has no hit. Read `SixFunctors/ProEtale/FiniteCoefficient/Derived/LocalizeConstructible.lean` and the relevant declarations in `LocalizationFiniteTor.lean`. In particular `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedFunctor_lowerStar_of_isClosedImmersion` requires the ambient scheme to be of finite type over a field and does not state the explicit partition assertion or the cohomological interval assertion. The adjacent pullback and Tor-amplitude results do not jointly supply all clauses with the item's hypotheses either. They are not an exact attachment. No source declaration containing sorry is treated as finished.

## WANTED

None. All documents used below are present locally.

## What was wrong and what changed

The item had an empty proof. Its source points to the finite-stage paragraph of `prop-sf-open-closed-triangle-all-stages.proof.md`, but that paragraph concentrates on comparison of the localization triangle; it does not spell out this lemma's finite partitions or unchanged cohomological interval. The seven steps provide those details using existing DAG statements. The proof is marked agent-written, with the blueprint as its parent and the Stacks places recorded at each step. There is no statement dispute and no hypothesis was added.

The important hypothesis check is retrocompactness of the open complement: exact closed direct image on the pro-etale site is not asserted for an arbitrary complement. Step 1 derives quasi-compactness of this complement from the Noetherian hypothesis before the support lemma is applied. On the geometry side the pulled strata are actual fibre products, not arbitrary strata with set-theoretic image contained in another piece. The closed-side strata retain their original scheme structures.

## Blueprint and reuse searches

Read the chapter `sec-smooth-purity`, the unit `sk-prop-sf-open-closed-triangle`, the current main-20261015 proof of `prop-sf-open-closed-triangle-all-stages`, and the item's original source/provenance. The ancestor command returns `prop-sf-open-closed-triangle-all-stages`; its finite-stage constructibility detail and sheaf-to-complex passage are the places realized here. The unit route is unchanged.

Searched the whole DAG by the source tags 09AA, 09BM and 09AH and by the local-model, immersion permanence, stratification, exact-functor, and inverse-image notions. Ran `tools/blueprint_refs.py search` for `closed immersion`, `constructibility partitions`, `exact functor`, `finite constructibility`, `pullback locally constant`, `constructible preimage`, `pullback of a stratification`, and `inverse images`. The existing stratification-pullback node was found and used; no blueprint node states the entire item in another form, so `same_as` remains empty. The existing exactness, support, local-model, geometry, and homological algebra nodes suffice. No new statement duplicates a clause of this item.

Ran the required msearch command with two semantic phrasings, LeanSearch, Loogle and Mathlib grep; the command's records are in `searches.jsonl`, and the new records were appended without deleting the inherited genuine searches. The hits were read. They concern Zariski structure-sheaf modules, etale-site infrastructure, or topological constructible sets; none states this pro-etale finite-coefficient module assertion. In particular the constructible-image hit has finite-presentation and compactness hypotheses and does not state constructibility of a sheaf. All five new searches returned normally; no unavailable search is reported as absence.

## Not duplicates

No new nodes are proposed, so there are no new/existing-node pairs to distinguish.

## Review by Q54

I read the source statements in Stacks `proetale.tex`, labels `lemma-closed-immersion` (09AA), `lemma-closed-immersion-complement-retrocompact-exact` (09BM), and `lemma-ses-associated-to-open` (09AH). The first gives the counit for every closed immersion, the second requires the retrocompact complement, and the third confirms the same quasi-compact-open setting. These support the item's sheaf-level argument with its actual Noetherian hypothesis; none requires a reduced closed subscheme. I also read `sites-modules.tex`, `lemma-pullback-locally-constant` (093R); `morphisms.tex`, `lemma-inverse-image-constructible` (054I); `schemes.tex`, `lemma-composition-immersion` (02V0); `properties.tex`, `lemma-locally-Noetherian` and `lemma-Noetherian-topology`; `topology.tex`, `lemma-Noetherian-quasi-compact` (04ZA); and `derived.tex`, `lemma-right-derived-exact-functor` (015F). These are general inputs to the expanded blueprint argument. There are no new nodes whose sources or independent statements need a further check.

For step 1 I opened `lem-weil-pbc-noetherian-open-subscheme-noetherian`: its statement explicitly gives that any open subscheme of a Noetherian scheme is Noetherian and quasi-compact. Applying it to the open intersection with each affine gives relative quasi-compactness of j, rather than inferring relative quasi-compactness merely from U being quasi-compact. Applying it to intersections of two opens proves retrocompactness. The definition in `def-weil-constructible-subset` then makes every open-minus-open expression constructible. This is the elementary two-intersection argument, not an uncited Noetherian geometry theorem.

For step 2 I opened `prop-weil-pbc-proetale-constant-ring-map`, `lem-weil-pbc-proetale-immersion-limit-preservation` and `lem-weil-pbc-proetale-ringed-open-closed`. The first has the actual canonical constant coefficient map as an isomorphism. The second explicitly gives additive exact module inverse image along a locally closed immersion with identified rings. The third states exact i_* and both identities used later, i^{-1}i_*=id and j^{-1}i_*=0. The coefficient isomorphism and quasi-compact complement hypotheses have been supplied before using these statements. No theorem about a ringed pullback with a noninvertible coefficient map is substituted here.

For step 3 I read the four cited statements: `lemma-constructible-pullback-stratification` gives exactly the actual fibre-product partition with the stated inverse-image subsets; `lem-pur-scheme-constructible-preimage` gives constructibility for these subsets under an arbitrary scheme map; `lem-weil-pbc-left-exact-site-inverse-image-tensor` gives composition comparisons for inverse images and says they are monoidal; `lem-exc-proetale-pullback-locally-constant` explicitly preserves the same finite module models on the base-changed cover. The base-change functors defining pro-etale inverse image preserve finite limits and covers as recorded in the statement's existing inverse-image/operations definitions. For the commuting square, the two composite scheme maps coincide by the fibre-product equations. The module comparison is justified explicitly: its coefficient paths agree on constant sections and its naturality for the action map proves linearity. This addresses the risk of citing only an abelian comparison for a module assertion.

For step 4 I opened `lem-weil-pbc-proper-fp-permanence` and use only its clause (e), which actually states composition of immersions. I do not take an immersion theorem from a definition node. The definitions of closed immersion and locally closed subset then justify the written V' intersect i(D) calculation. The constructibility of these subsets and of U was proved in step 1. Pairwise disjointness and coverage follow from injectivity of the closed embedding and the original partition of Z. No strata are made reduced, and no factorization is inferred merely from containment of set-theoretic images.

For step 5 the same composition-comparison node and the ringed open-closed statement say exactly what is required: the restriction on T_mu is t_mu^{-1}i^{-1}i_*N, hence t_mu^{-1}N by the counit, and the restriction on U is zero. The local constancy on T_mu is the input witnessing partition of N. The zero sheaf has finite zero-module model. Thus this step proves constructibility rather than citing a new node restating that clause.

For step 6 I opened `lem-weil-pbc-exact-functor-derived-factorization`, whose statement gives the triangulated factorization and a termwise representative for every complex, and `lem-weil-pbc-exact-functor-derived-functor`, whose statement identifies this with both total derived functors on the unbounded categories. Exactness was established in step 2, in the ambient abelian module categories. There is no assumption that a bounded constructible derived object has a bounded representative with constructible terms.

For step 7 I opened the three cited definitions. The cohomology definition explicitly gives ker(d)/im(d), the support definition is exactly the nonvanishing degrees, and finite-torsion constructibility defines D^b_c by finitely many nonzero constructible cohomology sheaves. Preserving kernels, images and their quotients under an exact functor yields the displayed natural isomorphism in a few lines. The zero outside [a,b] conclusion follows from preservation of zero. Steps 3 and 5 then supply constructibility of each cohomology sheaf. This checks the asserted cohomological interval, not a different Tor-amplitude interval.

I checked the empty schemes/empty strata (remove empty members), Z empty (i_* is zero and the open is X), U empty (the original partition on Z supplies the whole partition of X), the zero sheaf/complex, an interval with a>b, and a nonreduced closed subscheme. For example a nonreduced closed subscheme still has the same closed embedding topology and the pro-etale counit of 09AA; no step uses nilpotent vanishing or reduced strata. All cited hypotheses remain valid. I checked that each proposed proof dependency has no path back to this item in the existing statement/proof graph. Each proof step is below 2000 characters. During review I made the coefficient-action comparison in step 3 explicit and made the affine-intersection criterion in step 1 explicit. No independent worker or sub-agent was started, as required by this direct-delivery brief.

The cross-unit citations are generic geometry, site, support and exact-derived-functor tools, not replacements of the unit's localization route. Their specific purposes are recorded individually in `split_report.tool_uses` for the maintainer to judge. All 19 quotations in `citations.json` are literal substrings of the statements I read.

## Unfinished work

None within this one-level stage-1 item. The reused nodes retain their own existing proof/status records; no claim that all their downstream Lean proofs are finished is made.

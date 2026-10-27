# Worker report: lem-sp-stratified-reduction-postnikov-comparison

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-stratified-reduction-postnikov-comparison.json: statement split into six proof steps; no Mathlib match for the whole assertion.
- citations.json: one verbatim statement quotation for each of the 17 step/node citations.
- report.md: this report.
- searches.jsonl: actual msearch output log, created by the search command.

No new nodes and no new Mathlib leaves. The sandbox initially contained only dispatcher brief markers, so there was no previous proof or report to replace and no delivery to resume. No active deliver.py invocation for this item was found before starting. The statement, statement dependencies, source, creation record and blueprint ancestry are retained.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for Postnikov, stratified reduction, stratified_reduction, postnikov_comparison and finite_matrix_reduction. TwoColimit.lean discusses a Postnikov argument for descent of rational coefficients through finite extensions. That concerns different coefficients and a different conclusion, and supplies no attachment for this integral finite reduction comparison. Other stratification matches concern geometric gluing. I did not treat sorry declarations as finished proofs, and ran no compiler or Lake command.

## WANTED

None. The necessary Stacks sources and the blueprint source are present locally.

## Findings and repairs

The original node was statement-only and mathematically usable. No statement dispute or hypothesis correction was necessary. The blueprint file sk-def-sp-normalized-towers-reduction.md contains the parent theorem's assertion and has no proof paragraph. The ancestor's reviewed split allocates restriction and Postnikov induction to this item. I therefore mark this proof agent-written, with explicit Stacks sources for its ingredients, rather than attribute an unwritten proof to the blueprint.

The distinction between completed integral coefficients R_W and the discrete finite constant ring sheaves R_{W,n} is retained. The inverse-image coefficient identifications are the ones explicitly specified in the item. No flatness of R_T -> R_{T,n}, truncation/reduction interchange, finite global stratification extracted from a non-qcqs scheme, or torsion-freeness of local models is assumed. The given finite global partition supplies exactly the global constructibility conclusion.

During self-review I made the finite-stalk passage an explicit citation of lem-weil-pbc-proetale-finite-model-stalks. Local finite generation over the finite scalar ring first supplies finite constant models; this cited statement then gives the geometric-stalk conclusion. I also made the empty-scheme convention explicit: its partition can be represented by one empty stratum.

## Search record and reuse

The item's inherited Q92 searches are retained as historical searches. My six searches were run with msearch.py and their actual results are in searches.jsonl: Loogle on DerivedCategory and CategoryTheory.Sheaf; a grep for Postnikov/constructible/locallyConstant in Algebra/Homology; LeanSearch for exact restriction and scalar reduction on fixed strata; two differently phrased LeanFinder searches; and a grep for map_distinguished_exact and mem_homologicalKernel_trW_iff in CategoryTheory/Triangulated. All services returned successfully. The first semantic phrasing returned fraction factorizations and unrelated exactness results; the second found homological-functor exactness, which covers an existing dependency rather than this item. I read HomologicalFunctor.lean, lines 72-95, including map_distinguished_exact at line 86: its conclusion is exactness of a mapped distinguished short complex, with no ringed-site reduction or constructibility conclusion. The whole item is not a one-line specialization of those hits.

I searched the entire DAG by relevant titles and statements and blueprint_refs.py by Postnikov, stratified reduction and finite type sheaves. The existing finite scalar-matrix reduction, arbitrary-site Serre closure, canonical truncation triangle, exact module inverse image, tensor inverse-image comparison and K-flat localization already provide the supporting lemmas. Creating copies of them would be duplication.

## Not duplicates

No new nodes. The split reuses lem-sp-integral-local-model-finite-matrix-reduction for individual local-model reductions and proves the bounded-complex assembly here. It does not move a clause of this item into a new node. The Noetherian-only finite coefficient model comparison lem-pe-finite-coefficient-model-comparison is not used to bypass the absence of a Noetherian hypothesis on T.

## Review by Q103

I read the item, its chapter and unit, its parent node's proof and review, the main-20261015 reduction-tower source, and the statements of every dependency used in the six steps. I read Stacks sites-modules.tex at lemma-flat-pullback-exact (04JC), lemma-tensor-product-pullback (03EL), and lemma-kernel-finite-locally-constant (093U), including clause (3) and its proof. I read sites-cohomology.tex at lemma-K-flat-resolution (06YS), lemma-pullback-K-flat (0G7E), and lemma-derived-base-change (06YY); and derived.tex at lemma-cohomology-homological (05RS) and remark-truncation-distinguished-triangle (08J5). No new-node source needed checking because no new node is created.

Step 1 uses lem-trf-geometric-inverse-image-exact specifically for modules with transported inverse-image scalar action. Its statement gives exactness for arbitrary small sites, so it applies to the two coefficient rings here without assuming a flat quotient. lem-sp-exact-functor-preserves-homology(c) gives the precise natural identification of homology after inverse image. The abstract-derived-category definition gives the cone matrix and its negative projection, which I check termwise to obtain triangle compatibility. This is a calculation with the specified cone, not an unsupported preservation assertion.

Step 2 uses the flat-term part of lem-pc-kflat-resolution and the full ringed-topos generality of lem-weil-pbc-ringed-topos-kflat-pullback. The latter's ring map is the supplied coefficient isomorphism; its hypotheses do not demand any scheme-theoretic flatness of the immersion. lem-pur-derived-change-of-rings identifies the two derived reductions with the displayed complexes. Clause (1) of lem-pur-proetale-inverse-image-tensor-comparison actually states the ordinary isomorphism and its pure-tensor formula, rather than merely defining a tensor map. The formula is checked against the finite target scalar action, differential, shift sign and off-diagonal cone map. The resolving-class equivalence is explicitly in lem-weil-pbc-site-derived-tensor-descent; clause (2) of lem-weil-pbc-localization-universal-property descends natural transformations to the desired target D(R_{S,n}). Thus independence of resolutions and naturality are supplied by statements of cited nodes. Compatibility with the connecting map follows from naturality and the verified shift square.

Step 3 cites lem-weil-pbc-truncation-triangle, whose statement includes exactly tau_{<=q-1}, tau_{<=q}, H^q[-q] and functoriality. The definition of the standard truncation supplies its cohomology, and the abstract derived category inverts the resulting endpoint quasi-isomorphisms. I checked q=r and q=s, including a complex concentrated in one degree: the first term is zero and the last is the restricted reduction of M. This does not identify truncation with a derived tensor product.

Step 4 uses the statement, not the proof, of lem-sp-integral-local-model-finite-matrix-reduction. It applies on every scheme S, to finitely presented scalar models including torsion, and explicitly gives finite A_n, locally constant finite-type cohomology in degrees -1 and 0 and common covers for all n. Shifting by [-q] gives q-1 and q. For a free model only degree q is needed; for A/pi in a ramified coefficient extension both degrees can occur, which tests the sign and the necessity of the lower bound. The zero model and empty charts are explicitly included in the cited statement.

Step 5 uses lem-sf-derived-homology-long-exact to write the actual short exact kernel/cokernel sequence controlling H^k(X_q). Its two outer objects only involve objects already locally constant of finite type by induction or step 4. The statement of lem-weil-pbc-locally-constant-derived-serre provides all three closure operations, on any small site, requiring only a Noetherian scalar ring. A_n is finite by step 4, hence has finitely many ideals and is Noetherian. No property of T is substituted for this hypothesis. The induction starts with zero and gives [r-1,q] at each stage. Shifting fourth terms preserves local finiteness, although their degree bounds shift; the range [r-1,s] is claimed only for the final unshifted term, as in the item.

Step 6 combines step 1's exact cohomology restriction with step 5. Finite generation over finite A_n gives a finite underlying set by a surjection A_n^t -> N. The cited proetale-finite-model-stalks statement applies to these finite constant models on an arbitrary scheme; def-weil-proetale-constructible-sheaf requires precisely the given actual immersions, constructible locally closed finite partition and finite stalks. There is no new partition as n or k varies. Zero M, empty T, a single stratum and disconnected/non-qcqs schemes with an explicitly supplied partition all satisfy the same argument.

Every cited dependency's closure was checked not to return to the item. Generic off-unit tools are explained in split_report.tool_uses; definitions, Mathlib leaves and Lean-closed nodes are used as such. No unit route is replaced, no SGA source is cited, and no node statement is edited besides adding the proof to this item. Each proof step is shorter than 2000 characters, so no long step hides an additional sublemma. The lengthy part of the mathematics, the scalar two-term model, is already the statement of its separate existing node.

## Unfinished work

None for this stage-1 split. Its unsplit supporting node lem-sp-integral-local-model-finite-matrix-reduction remains a separately assigned item; I have not altered or split it.

## Validation

The resumed required deliver.py --no-push completed with exit 0 and printed OK (not pushed), at 5f451bd1ecf. The server preflight passed on the full six-step split, report and 17 citations, and saved its durable dry-run receipt. After the continuation review below, the final report is checked again before pushing.


## Continuation review by Q103

The interrupted attempt already contained the completed split, report, citations and six actual search results. I retained those files and queries, read searches.jsonl and the recorded result names, and started with the required dry run; its tool session exited successfully before any push was attempted. Comparison with the current read clone found only the intended proof, status, searches, origin and split-report additions; the live item is still unsplit and has no repair note.

I reopened the chapter, normalized-towers unit, parent reduction-tower proof, the blueprint reduction assertion and every statement cited by the six steps. The source text at 04JC distinguishes exact inverse image from flat ringed pullback: step 1 uses transported inverse-image scalars, which meets precisely that distinction. At 03EL the tensor comparison is functorial, and at 06YS, 0G7E and 06YY the resolution and pullback results cover unbounded complexes with flat K-flat representatives, so step 2 does not silently assume a flat finite quotient. At 08J5 the second displayed triangle has cohomology in degree a+1, giving exactly step 3 with a=q-1. At 05RS and 093U(3), the long exact sequence and all three Serre closure operations give step 5's displayed kernel/cokernel short exact sequence. The finite ring supplies the Noetherian hypothesis; the scheme need not do so.

I checked the finite-matrix node's actual statement for step 4, including the derived-object isomorphism, finite scalar modules, common charts and degree bounds. Shifting its degrees -1,0 by [-q] gives q-1,q, so the induction's final interval is [r-1,s]. The free rank-one model, a torsion model A/pi, zero cohomology and the empty stratum test these bounds and the finite-stalk passage. Step 6 cites the finite-model stalk theorem and the full constructibility definition, including actual immersions and the same global partition. All 17 citation quotations remain verbatim substrings of the current cited statements. No proof step exceeds 2000 characters.

The source search in lean/WeilConjectures still finds no declaration for the exact item tag or its reduction-comparison names; the lone Postnikov comment is in TwoColimit.lean and concerns rational coefficient descent. I also reopened Mathlib's map_distinguished_exact: it states exactness after a homological functor, not the ringed-site comparison and common-stratum conclusion here. The whole-blueprint searches for Postnikov and stratified reduction supply no duplicate of this item. No new mathematical correction or supporting node was needed on continuation.

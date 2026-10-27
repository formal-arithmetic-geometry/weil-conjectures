## Worker report

Files written: `dag/nodes/sec-purity-real-sheaves/lem-tw-representable-slice-localized-ringed-morphism.json`, the item, statement with a six-step proof, no Mathlib match; `citations.json`, the per-step statement quotations; this report. The search wrapper wrote `searches.jsonl` in this sandbox. No Lean, library, repository, launcher, chapter or unit file was changed.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. The proof uses existing DAG statements, and its explicit pullback/Hom calculation is an elementary adjunction calculation rather than a new lemma. No clause of the item was moved into a new node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, representable slices, localized ringed morphisms and slice adjunctions found no declaration proving the entire comparison. Existing localized restriction/extension declarations do not state the item. No sorried declaration was treated as a finished proof.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Corrections and remaining work

The statement and its hypotheses are unchanged. The live item was unsplit with an empty proof. I replaced its inherited unavailable/unrun search records with the actual queries and results recorded by msearch for this dispatch. The first Loogle query contained an unknown identifier; I retained that diagnostic and ran the successful `CategoryTheory.Over.post` query afterwards. There is no outstanding mathematical claim hidden behind an attachment or an unavailable search.

The split follows Stacks `sites.tex`, Tag 03CF (`lemma-localize-morphism`), the middle diagram and the final product calculation. Rather than leaving the middle diagram implicit, it writes down the right adjoint on slices and its Hom bijection. The representable identification is Tag 04D3 (`lemma-pullback-representable-sheaf`). Ring maps are compared using `sites-modules.tex`, Tags 04J0 (`lemma-localize-morphism-ringed-sites`), 04IF (`lemma-localize-morphism-ringed-topoi`) and 04J7 (`lemma-localize-morphism-compare`). I also read `sites.tex` Tag 04IU (`lemma-localize-morphism-compare`), whose omitted details are resolved by the unit-normalized adjunction calculation here.

## Searches and existing nodes

The Mathlib searches are exactly the logged msearch queries. The two semantic phrasings returned local preimages, local morphism properties, general continuous sheaf adjunctions and dense-subsite equivalences. These do not identify the localized inverse image with the arrowwise inverse image on representable slices, much less the coefficient map. The source grep found `GrothendieckTopology.overPullback` and `overMapPullback` in `Sites/Over.lean`; I read their definitions (lines 288 and 427), which are restriction and change of base object, not this comparison for a functor between sites. I read `Sites/SubcanonicalOver.lean`, whose result is subcanonicity of the localized topology only. The follow-up grep located `Over.post` in `Comma/Over/Basic.lean:423` and the sheaf inverse-image adjunctions in `Sites/Pullback.lean:55-85`; neither supplies the item as an exact match or one-line specialization. Thus the item is not a Mathlib leaf.

DAG searches covered the statement, title and source fields for slice adjunctions, inverse images, representables, Tags 03CF, 04J0 and 04IF, and localization comparison labels. Blueprint searches used `slice`, `localized`, `03CF` and `representable` across all chapters. They found no blueprint node stating the item. They did find all the existing tools used below, including the localized-sheaf fibre equivalence, the localize-ringed-site-morphism square, and normalized slice set pullback. `blueprint_refs.py ancestor` gives `lem-tw-dual-negation`; the inherited precise `from.place` and `via` are retained. The blueprint's first sentence identifies the dual stalk with the dual representation; this item is the generic chart tool needed by that realization, not a replacement of the linear-algebra route. Off-unit generic tools are declared in `split_report.tool_uses` for the maintainer to judge.

## Not duplicates

No new nodes were created. Existing general slice and localization statements are cited, rather than duplicated. In particular `lem-weil-pbc-slice-site-localization` states commutation with restriction, not the full inverse-image formula on arbitrary slice objects; `stage3-slice-sheaf-inverse-image-equivalence` likewise only states finite-limit preservation and restriction comparisons. The present proof supplies the missing arbitrary-slice comparison. The arbitrary-sheaf slice ringed square nodes do not identify the given continuous functor on localized sites with that square; the explicit right-adjoint comparison supplies that identification here.

## Review by Q28

I read the item against Stacks 03CF and 04D3, with the two displayed structural maps in 04J0 and 04IF and their equality in 04J7 open. The original assumptions give continuous functors because coverings and all finite limits are preserved. Subcanonicity is used exactly where the slice base is the representable itself, rather than its sheafification. Both sites are small in the sheaf universe, so the slice and element-site categories and all finite products and pullbacks used here stay within the specified universes. No coefficient flatness, invertibility, points, enough points, or exactness of a module pullback is assumed.

Step 1 uses the actual statement of `lem-pur-site-representable-algebraic-pullback`: c_V is an isomorphism with adjunct beta(a)=u(a). The statement of `lem-weil-pbc-localized-sheaves-over-representable` gives the quasi-inverse by fibres, not just an unspecified equivalence; this is precisely what the product-restriction identification takes from it. `def-pur-localized-ringed-site` defines the arrows, coverings and sectionwise restrictions, so the comparison of the element site at h_V with C/V is literal. The remaining part of this step is just taking a fibre of a product.

Step 2 cites `lem-weil-pbc-site-sheaf-sets-limits-sectionwise` for existence and sectionwise computation of the pullback T, and `lem-weil-pbc-left-exact-site-inverse-image-tensor` for the genuine adjunction L ⊣ P. The representable comparison statement specifies that c_V is adjunct to beta; that is the exact equality needed to transpose qt=c_V Lphi. The step explicitly writes the two inverse functions on Hom sets and their slice condition. There is no appeal to a proof-only construction or a nonexistent slice-adjunction theorem.

Step 3 uses the fibre formula from the localized-sheaf equivalence and the definition of continuous pushforward from `def-weil-pbc-sites-and-cohomology`. It computes both sides at every (W,a) and on every restriction b, so it is an identification of functors, not a pointwise comparison without naturality. The localized morphism and its direct-image square are supplied by `lem-weil-pbc-localize-ringed-site-morphism`. Finally `lem-weil-pbc-conjugate-iso-unit-equation` explicitly asserts uniqueness and invertibility of the unit-preserving comparison of two left adjoints to one right adjoint; this proves exactly the natural inverse-image isomorphism needed.

Step 4 uses finite-limit preservation from the inverse-image node and the adjunct normalization from the representable node. It writes the two coordinates of the slice unit and therefore identifies the chosen comparison, not merely some natural isomorphism. `lem-weil-pbc-slice-set-pullback-isIso` states invertibility of the specified inverse mate of the sectionwise-identity square; `lem-weil-pbc-localize-ringed-site-morphism` states the restriction comparison for that same localization. The coordinate calculation matches this mate and the displayed product isomorphism.

Step 5 uses the statement of `lem-weil-pbc-ringed-sheaf-slice-adjunction`, which identifies R_A with the sectionwise ring R(U), and the localized-ringed-site definition for the restricted rings. The localize-ringed-site-morphism statement explicitly gives its structural map as restricted c after the restriction isomorphism. The two formulas are written in the proof and agree on fibres; checking operations is naturality with the finitely many product diagrams for ring operations. This elementary assembly does not use the definition of a ringed morphism as if it proved a comparison theorem.

Step 6 uses the module interpretation and sectionwise restriction stated in the ringed-sheaf-slice node. The module-adjunction node actually states the tensor-formula pullback is left adjoint to the direct image with action via the adjunct of c. Step 5 has already identified that coefficient map, so both scalar actions coincide. The conjugate-iso unit equation then gives the canonical module isomorphism. Compatibility with restriction follows after taking adjoints: both maps become sectionwise restriction with this same scalar action. The localized-ringed-site-morphism node states the corresponding module square. This avoids an uncited assertion that some arbitrary equivalence preserves an unmentioned tensor construction.

I checked the B--E failure modes against these files: all quotations in citations.json are verbatim portions of the cited statements; uses and proof_deps agree; no new node is elementary, duplicate, or a renamed clause because there are no new nodes. Every step is shorter than 2000 characters. The small cases checked were u=id (T reduces to the original sheaf over the representable, and the comparison is the unit-preserving identity), V terminal (the comparison reduces to L itself), the empty sheaf in a slice (the pullback/Hom bijection still holds), and a zero coefficient ring (all maps remain unital maps of zero rings where applicable, with no use of nonzero scalars). Non-faithful u causes no problem: T has pairs indexed by each a and never identifies distinct arrows merely because u(a) agrees. This is why the fibre at a is retained throughout. I corrected the step-1 source tag to 00Y1 after checking the Stacks tag index (the label lemma-essential-image-j-shriek was already correct). I corrected the initial draft's citation for direct-image precomposition by adding the definition node explicitly; the proof uses its statement, not an implicit convention.

No part remains unfinished. The required server dry run and push follow this report; acceptance is recorded by the delivery command's result.

## Validation

The initial `deliver.py --no-push` exited successfully with server preflight passed. After the source-tag correction I rerun the required dry run before pushing the final files. No local DAG checker or compiler was run.

## Worker report

Files written: dag/nodes/sec-smooth-purity/lem-kun-grothendieck-derived-coproducts.json (statement, split, no new nodes). citations.json records the statements actually used. No new Mathlib leaves. The statement is unchanged.

## Attachments

No attachment for the item. The existing closed node lem-weil-pbc-kinjective-functorial-existence already records CochainComplex.kInjectiveResolutionFunctor, CochainComplex.toKInjectiveResolution, CochainComplex.monoQuasiIso_toKInjectiveResolution_app, and CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj. I read their bodies in WeilConjectures/CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean:138–164; they provide replacement, not the coproduct theorem. Products.lean gives products and cannot attach this coproduct assertion.

## Sources and searches

Read injectives.tex Tag 07D9 (lemma-derived-products), including its displayed Hom calculation; Tag 079P (theorem-K-injective-embedding-grothendieck); derived.tex Tag 070I (lemma-K-injective), assertion (3). Read the chapter and unit records and the master blueprint lem-kun-0f11, Proof Step 2. The split supplies precisely the coproduct infrastructure invoked there. Whole-DAG searches by 07D9 and by coproduct/homotopy and K-injective terminology, and blueprint_refs searches for coproduct, termwise direct, 07D9, K-injective and homotopy category were read. Existing module-only or countable-sum results do not cover arbitrary Grothendieck categories and arbitrary small index sets. No new node is necessary: the homotopy assembly is written directly.

The item searches were run through msearch.py and appended faithfully. LeanFinder twice returned Grothendieck complexes, t-structure and localization infrastructure, without the coproduct assertion; Loogle found no preservation match. Greps in DerivedCategory and Localization found no coproduct assertion. LeanSearch returned Internal Server Error and is recorded unavailable. Source project searches by the blueprint id and by coproduct/direct-sum/preservation concepts found no complete project declaration of the item. The upstream master is not evidence of finished proofs.

## WANTED

None. Nothing remains unfinished in this one-level split. No disputed statement or change of the unit route was needed.

## Review by NA

I read the item against injectives.tex 07D9, assertions (1)–(2) and the coproduct half of its proof. All complexes remain unbounded, the index is a set in the chosen universe, and the category is arbitrary Grothendieck abelian. No coefficient-specific or bounded-below theorem is substituted.

Step 1 cites the actual small-colimit clause of def-sp-grothendieck-abelian and the differential/chain-map definitions of def-weil-abstract-derived-category. Its differential-square and chain-map equations are verified after precomposition with each coprojection. Step 2 writes the homotopy equation explicitly: choosing representative maps gives surjectivity; assembling the degree-minus-one component homotopies gives injectivity. This is a direct application of the degreewise coproduct property, so it is an elementary step rather than a new lemma. Neither step uses exactness of infinite sums.

Step 3 cites lem-weil-pbc-kinjective-functorial-existence, whose statement is for every complex in an arbitrary Grothendieck category and supplies exactly a quasi-isomorphism to a K-injective complex. I deliberately did not use prop-pur-kinjective-resolutions-exist, which only states a ringed-site result. This closed generic theorem is a tool from another unit, declared in split_report.tool_uses; it is the theorem 07D9 itself invokes and changes no unit route. The localization definition supplies the derived isomorphism and representation by complexes.

Step 4 cites lem-sc-kinjective-quasi-iso-comparison, opened and read in full: its statement says localization on Hom into any K-injective target is bijective, for an arbitrary abelian category, not merely sheaves. I also read Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:41–46. The only hypothesis needed is J K-injective from Step 3; neither S nor the K_i must be K-injective. The comparison square commutes because Q preserves composition; therefore its bijection is restriction along the actual coprojections, as required, not an unrelated Hom-set bijection.

Step 5 explicitly transports by postcomposition with the target isomorphism, which is bijective on both sides and commutes with restriction. For the empty family S is degreewise zero and both sides of the restriction bijection are singleton sets. For a singleton it reduces to the original complex; zero complexes and arbitrary unbounded families cause no change to any construction. Choice of homotopies is set-indexed and imposes no boundedness or finiteness condition.

I checked B–E point by point: no new statements, duplication, hollow data or unsupported leaf claims; every non-elementary invocation is an existing cited statement with verbatim quotation in citations.json; componentwise homotopy assembly is proved rather than hidden; no step cites the proof of another node; no new dependency requires the item. No correction to the mathematical statement was needed. The initial unsplit item had no proof; the five steps fill that gap without moving its conclusion into a child.

## Second reading by NA

- Item statement: checked injectives.tex Tag 07D9, lemma-derived-products (1)-(2); faithful coproduct clause for arbitrary small families of unbounded complexes in a Grothendieck abelian category. No statement dispute.
- Step 1: checked def-sp-grothendieck-abelian and def-weil-abstract-derived-category statements; small colimits supply the degreewise coproducts and precomposition verifies both differential equations and uniqueness. PASS, elementary.
- Step 2: checked the homotopy equation against the homotopy-category Hom calculation in 07D9; choosing representatives and assembling degree-minus-one maps proves both directions of the restriction bijection. PASS, elementary; no exactness or boundedness hypothesis needed.
- Step 3: checked the full statement of lem-weil-pbc-kinjective-functorial-existence against injectives.tex Tag 079P, theorem-K-injective-embedding-grothendieck; it supplies a replacement for every complex. Localization inverts that quasi-isomorphism. PASS.
- Step 4: checked lem-sc-kinjective-quasi-iso-comparison and Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:41-46 against derived.tex Tag 070I, lemma-K-injective (3); only the target is required K-injective. Composition makes the bijection the specified restriction map. PASS.
- Step 5: checked postcomposition and restriction commute by associativity; their bijections give precisely the coproduct universal property. Empty family gives singleton Hom sets, singleton family the original complex. Zero complexes and vector spaces over a field satisfy the same component equations; an empty scheme's zero category adds no exception. PASS.
- New nodes: none; no duplicate, elementary child, restatement, or unverified Mathlib leaf to remove.

Changes: removed split_report.tool_uses because delivery-errors C8 reserves tool authorization for the maintainer. The first review's sentence saying it was declared there is superseded by this correction. The dependency lem-weil-pbc-kinjective-functorial-existence is still cited: it is the general Grothendieck replacement theorem used by the source proof; the unit has no replacement theorem in this generality. The maintainer may register this cross-unit tool use if required. Independently reran a semantic search using homotopy-quotient vocabulary and a source search for preservation of coproducts/colimits; no exact declaration found. Recorded their actual summaries in the item, with raw search records in searches.jsonl. No mathematical step, statement, or citation changed; existing citations remain verbatim.

## Worker report

Q113, stage 1, 2026-10-22. Item: lem-sf-finite-kernel-constructible-localization.

### Files written

- dag/nodes/sec-smooth-purity/lem-sf-finite-kernel-constructible-localization.json: ten-step split, status split; existing nodes supply every non-elementary fact.
- citations.json: 31 exact statement quotations for all step/node pairs, checked against the current read clone.
- report.md: this report and direct-delivery self-review.

No new nodes; no new Mathlib leaves. Only the sandbox was written. No Lean, compiler, Lake, git command in the shared repository, or sub-agent was used. The delivery command will build the authorized delivery in its own worktree.

### Attachments

None. Searches for the exact blueprint tag in lean/WeilConjectures found no declaration. Concept searches found Etale.existsUnique_distTriang_supportedLocalization in SixFunctors/Etale/Derived/Localization.lean:252, read at lines 242–307. It is an ambient etale theorem with supplied exceptional-adjoint hypotheses; it does not state intrinsic pro-etale constructibility or preservation of this kernel adjoint on D^b_c. ClosedImmersionStages likewise covers closed full faithfulness, not every clause of this item. No partial result is submitted as an attachment.

### Literature and searches

No WANTED documents. Read GOAL.md; SETUP.md's fixed chapter, conditional unit route and free node levels; the worker brief, stage-1 contract, delivery-errors B–E in full, chapter sec-smooth-purity and unit sk-prop-sf-localization. Read the current main-20261015 prop-sf-localization-all-stages.proof.md (Finite stage and Vanishing), the unit _section.md, and sk-prop-sf-localization.proof.md. The proof realizes the finite-stage route and the ordinary-triangle/Hom argument; no SGA source is used.

Read Stacks proetale.tex: lemma-closed-immersion (09AA), lemma-closed-immersion-complement-retrocompact-exact (09BM), lemma-ses-associated-to-open (09AH), lemma-morphism-comparison (09A6), lemma-compare-constructible (09AK), lemma-constructible-serre (09B5), and lemma-compare-constructible-derived (09AL). Also read derived.tex lemma-adjoint-is-exact (0A8D) and lemma-right-derived-exact-functor (015F), and etale-cohomology.tex lemma-constructible-abelian (03RZ). Existing nodes carry these theorem interfaces; tags are not substituted for node citations. The older comparison-direct-image source's 099R is the comparison section; the precise direct-image lemma is 09A6. No existing dependency file is changed.

Ran blueprint_refs.py ancestor for the item; its ancestor is prop-sf-localization-all-stages. Searched the whole blueprint with kernel, constructible, adjoint triangle, constructible origin, counit cone, kernel constructible, right adjoint exact, support kernel and localization, and searched the whole DAG by statement concepts. The older pro-etale constructible-origin node fixes the global finite-field datum, so the proof instead cites lem-weil-pbc-finite-ring-constructible-derived-origin, whose statement explicitly permits every scheme and every finite commutative ring. The cone identification is already lem-sf-ordinary-triangle-counit-cone; it is not recreated. No blueprint node states this entire finite constructible kernel-restriction assertion separately.

Mathlib searches were run only through batch2/msearch.py for this group and item: LeanFinder (two phrasings), Loogle, grep, LeanSearch. Results and exact queries are retained in searches.jsonl and appended to the item's existing mathlib_searches without removing the earlier searches. The first semantic query returned scheme ideal kernels and affine-limit results. The second returned Scheme.Modules.restrictAdjunction, restrictFunctorAdjCounitIso and kerAdjunction; their displayed types concern O_X-modules or ideal sheaves, not finite-constant-coefficient pro-etale constructible categories. LeanSearch returned general abelian/sheaf/derived infrastructure, Loogle and the Mathlib grep returned no hit. These do not state the item or give it by a one-line specialization.

### Statement corrected

The only statement edit changes the reference def-weil-pbc-kinjective-resolutions to def-pur-kinjective-complex, with the corresponding statement dependency replacement. The former explicitly defines K-injectivity only in Mod(T_et,R), while the latter defines it for every small ringed site and therefore actually covers the pro-etale module category here. The objects, coefficient rings, hypotheses, maps and conclusions are unchanged. This is a reference repair, not an added mathematical assumption. No false proposition or missing geometric hypothesis was found in the item.

### What was wrong or incomplete

The imported child was statement-only. A direct use of the older sf constructible-origin node would have silently imposed its global finite-field hypothesis; this was avoided by the existing general finite-ring equivalence. The proof explicitly constructs the supported triangle in the unbounded ambient categories before using its outer terms to prove bounded constructibility. The actual counit-cone comparison is cited, rather than inferring an arbitrary cone isomorphism from a bare comparison of long exact sequences. The termwise closed counit and its signed shift compatibility are checked explicitly.

### Unfinished work

No part of the authorized stage-1 split remains. The delivery remains subject to server preflight and independent maintainer mathematical review. No claim of a Lean proof is made.

## Review by Q113

I reviewed this split directly against the source files and all 23 cited node statements. There are no new nodes whose proof is postponed and no new clause-relabeling nodes. The source for the item is main-20261015's Finite stage and Vanishing plus the unit's ordinary-triangle adjunction argument. I retained that route: ambient adjoints, ordinary localization, counit-cone identification, then constructible restriction. Every step is below 1000 characters; none of the non-elementary steps exceeds the 2000-character review threshold.

Step 1 uses finite-quotients and extension-integers-dvr for finiteness and the uniformizer factorization, not merely the coefficient definition. Since ell has absolute value strictly less than one, its uniformizer exponent is positive, so ell^n kills A_n and is invertible in k. Finite-type-over-Noetherian and Noetherian-open-subscheme-Noetherian verify quasi-compactness on each affine open, precisely the morphism condition needed by the ringed closed-kernel adjoint. The constant-ring-map statement gives the actual inverse-image coefficient identification. A field has only the two ideals, so its Noetherianity needs no extra theorem here. Z is closed finite type and U is a quasi-compact open in a finite-type scheme.

Step 2 reads the statement, not the proof, of ringed-closed-kernel-adjoint: it supplies all four unbounded adjunctions, the specified kernel counit, both invertible counits, and j^*i_*=0. Its complement quasi-compactness hypothesis has been verified in Step 1. Ringed-open-closed gives exact j_! and i_*, and constant-exact gives exact inverse images over the identified constant rings. No support triangle or constructible exceptional operation is assumed at this point.

Step 3 uses exact-functor-derived-triangulated for the four exact termwise functors. Ring-sheaves-grothendieck and kinjective-functorial-existence justify the hypotheses of canonical-right-derived-adjunction-shift for both (i_*,i^!_0) and (j^*,j_*). That statement is unbounded and for arbitrary abelian categories; the older bounded-below etale shift node would not suffice. Triangulated-right-adjoint explicitly requires unit/counit shift compatibility, which is why the preceding citation is present. K-injective-total-derived-linear requires an additive A-linear sheaf functor and resolutions, not a linear resolution selection. Kernels, inverse image and the sheaf Hom bijection are A-linear, so it applies to i^!_0.

Step 4 takes the short exact sheaf sequence from ringed-open-closed, applies it degreewise, and invokes complex-ses-triangle, whose statement gives the actual first two arrows of the resulting distinguished triangle. This is a triangle for every unbounded test M. Neither a bounded representative nor a finite-Tor hypothesis enters.

Step 5 uses the cone clause of the triangulated-category definition and the statement of ordinary-triangle-counit-cone. All hypotheses of that lemma have been supplied by Steps 2–4: exact functors, four adjunctions, invertible closed/open counits, mixed vanishing, and the ordinary triangle for every ambient test object. Its conclusion gives beta v = u and beta invertible; transporting the last arrow as w beta^{-1} retains precisely the actual maps e and u. Its other conclusion gives the Hom vanishing in all shifts; it is stronger than the constructible specialization needed here. This is not a citation of the weaker bare existence statement of proetale-support-triangle to justify prescribed maps.

Step 6 uses finite-ring-constructible-derived-origin, which states an equivalence with intrinsic bounded constructible pro-etale complexes and every cohomological interval, for any scheme. Cor-fin-deligne-open-finite-coefficients supplies exactly bounded constructibility of the etale Rj_* on finite-type schemes over any field and rings killed by an invertible integer. Comparison-direct-image is applied only to the bounded-below etale G' and qcqs j, as its statement requires. This avoids applying a D^+ theorem to an arbitrary unbounded object and avoids the fixed finite-field scope of the older sf comparison node.

Step 7 uses constructible-derived-subcategory for the triangulated etale category, finite-ring-derived-origin for fullness and essential image, and exact-functor-derived-triangulated for the actual comparison functor. Lifting a map by fullness and taking its image cone proves the claimed closure on the intrinsic side. No definition is used as the sole justification for triangulated closure.

Step 8 is elementary from the intrinsic sheaf definition and the exactness/identities already cited: pull back the finite stratification and its finite locally constant covers; for i_* append the complementary open stratum where the sheaf is zero and use i^*i_* = 1. All locally closed subsets of the Noetherian schemes in use are constructible, so the new strata qualify, including empty ones. Exactness makes H^q(FK)=F H^q(K) and preserves the original finite support interval. No assertion about all pro-etale sheaves being classical is used.

Step 9 is elementary assembly: the supported triangle has two constructible vertices by Steps 6 and 8; triangulated closure from Step 7 makes its fibre constructible. Applying exact constructible-preserving i^* and the ordinary closed counit gives Ri^!_0K itself. Full subcategories have precisely the ambient Hom sets, so their adjunction bijections, units and counits are literal restrictions. This is not a use of the definition of an exceptional inverse image to assume the preservation being proved.

Step 10 reads the termwise counit clause of ringed-closed-kernel-adjoint and the exact-derived-adjunction definition, which records the actual localized unit/counit. The degree-r counit at P[m] is exactly the degree-(r+m) counit at P; both differentials are multiplied by (-1)^m. Naturality therefore makes its inverse a chain map and proves shift compatibility before localization, not just an objectwise identification after passage to the derived category.

I tested U empty (i identifies the entire support, open terms vanish) and Z empty (closed adjoint zero, open unit invertible), K=P=G=0 and X empty. I also checked nonreduced closed subschemes, where only the given ringed closed-immersion identities are used. For n=1 the result remains the finite residue-field case; for n=2 a non-flat residue module is permitted throughout, since the proof never tensors with it or requests finite Tor amplitude. For arbitrary non-algebraically-closed k the finite-ring origin theorem and open-image theorem retain their exact hypotheses; no Galois cohomological-dimension bound is silently substituted. The signed-shift check covers negative as well as positive m. No newly asserted mathematical lemma failed these tests.

The generic off-unit interfaces are declared with reasons in split_report.tool_uses; the localization route itself is unchanged. I corrected only the etale-specific K-injective citation in the statement and used the general origin theorem and canonical unbounded shift theorem in the proof. Every uses entry has an exact quotation in citations.json copied from its node statement, and proof_deps is their union. I did not edit any dependency, chapter, unit, imported provenance, maintainer record or target statement.

## Not duplicates

No new nodes. Existing nodes, especially ordinary-triangle-counit-cone and finite-ring-constructible-derived-origin, were cited instead of duplicated.

### Dry-run repair

The first dry run refused the Step 1 constant-ring-map quotation because the exact sentence “Then $c_u$ is an isomorphism.” was shorter than its 40-character evidence minimum. I replaced it with the full node statement, which specifies the constant-section-induced map, its invertibility and its agreement with the actual module coefficient structure map. The proof itself is unchanged.

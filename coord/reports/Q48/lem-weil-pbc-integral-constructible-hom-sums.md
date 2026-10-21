# Q48: lem-weil-pbc-integral-constructible-hom-sums

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-constructible-hom-sums.json: existing statement, now split; no matching Mathlib theorem found. Its statement, statement dependencies, creation provenance and blueprint reference are preserved.
- citations.json: verbatim statement quotations for every node used in every proof step.
- report.md: this report. searches.jsonl contains the six searches made by Q48 through msearch.py.

No new nodes, no Mathlib leaves, and no unit edits.

## Attachments

None. Searches for the item id and its blueprint docstring tag in lean/WeilConjectures found no declaration. Searches by constructible/adic/pro-etale and Hom/coproduct notions found related finite-coefficient and condensed compactness infrastructure, which does not state this integral continuous-coefficient assertion for arbitrary uniformly bounded-below derived targets. No existing sorry-bearing declaration was treated as a finished proof. Only the supplied live read clone was used.

## WANTED

None. All sources used are in the supplied literature.

## Problems and changes

The imported statement is consistent with Bhatt–Scholze Lemma 6.8.12; no statement dispute or correction is needed. Its original proof was empty. The DAG already has the stronger lem-weil-pbc-integral-constructible-bounded-below-compactness: a canonical isomorphism of global derived Hom objects for every small uniformly bounded-below family. Creating another compactness node would duplicate it. The present split instead gives the argument passing from that existing theorem to all cohomology groups and checks the actual shifted-coprojection map.

The original source pointer mentions shifted internal Hom and K-injective interfaces. I used the existing all-degree sections-model theorem, not a scheme/Zariski-only shifted Hom statement, nor a degree-zero theorem as though it already stated every degree. The sections model assumes a tensor right adjoint, so I explicitly supplied the generic closed symmetric monoidal ringed-site theorem. All three off-unit homological-algebra tools are declared in split_report.tool_uses; none replaces a proper-base-change proof step. The unit key statement and realized fields do not belong to this item and were not changed.

The inherited Q01 Mathlib search records were retained. The six additional records reproduce exactly the Q48 logged tool names and query strings. I read the results: algebraic AdicCompletion sums do not assert the sheaf theorem; derived-category factorization and bounded-representative lemmas do not assert relative compactness; AB4 coproduct infrastructure concerns the target-side cohomology passage; the second semantic phrasing returned scheme quasi-compactness statements. Both targeted source searches and the Loogle query had no hits. Thus there is no exact attachment or Mathlib leaf for this item.

## Unfinished work

None for this stage-1 split. Existing cited nodes remain responsible for their own proofs; this delivery neither claims their Lean proofs are closed nor re-splits them.

## Not duplicates

There are no new nodes, hence no new/existing same-tag pairs requiring comparison. In particular, the stronger bounded-below compactness theorem is reused rather than restated as a child. Searches across the whole DAG and blueprint for the item notions and source place found no blueprint node stating this exact cohomological assertion. The ancestor remains thm-weil-pbc-finite-extension, historical sentence “Choose an integral lattice for K”, with the inherited via chain. The current main-20261015 proof uses the integral isomorphism followed by rational transport; the historical Ext denominator argument is auxiliary to that same integral-lattice passage, not a replacement route.

## Review by Q48

I read Bhatt–Scholze Lemma 6.8.12, immediately after Lemma 6.8.11(3), and its reference to Lemma 6.3.14. The source asserts that global RHom out of a constructible integral object commutes with arbitrary sums of connective targets; the reused existing DAG theorem explicitly states the common-lower-bound version. Its statement has the same finite extension E/Q_l, valuation ring, uniformizer, noetherian finite-dimensional scheme with l invertible, completed coefficient sheaf and bounded constructible complete source as the item. The item already assumes the canonical continuous/completed coefficient identification, so no new comparison of coefficient categories is introduced. The continuous A_X-module category is not silently replaced with discrete or condensed E-modules.

In step 1 I opened both cited statements. The bounded-below compactness node states an isomorphism in D(A), uses global derived Hom rather than internal Hom, and explicitly allows any common integer lower bound. Hence its hypotheses hold for our small countable family without an extra vanishing or finite-generation condition on the M_i. The global-derived-Hom definition supplies exactly the scalar-valued functor and the constant-residue scalar map used in the proof. The word canonical refers to the map induced by G(iota_i), not an arbitrary isomorphism between its endpoints.

For step 2 I read the module cohomology-coproduct statement and Stacks injectives.tex, Tag 07D9, clauses (1)–(2). The node asserts preservation of the colimiting cofan by H^q for every integer q and arbitrary unbounded module complexes, including the empty family. It therefore applies directly to G(M_i); it requires no inference that these derived Hom objects share a lower bound. Applying H^q to the step-1 isomorphism and using the cofan identification proves the displayed module map, with its specified components.

For step 3 I opened all three cited statements, and read Stacks sites-cohomology.tex, the internal-Hom construction (08J7), the global-sections computation (08JA), and the adjunction/currying assertion (08J9). The closed symmetric monoidal statement is for any small ringed site, so it applies to the chosen small pro-etale site with coefficient sheaf A_X; its symmetry changes tensor-on-the-right into tensor-on-the-left. The sections model then really asserts H^n RΓ(H_K(M)) = Hom(K,M[n]) for all integers and naturality on K-injective target maps. It has no boundedness or flatness condition on M. I did not cite the scheme-specific lem-sc-derived-internal-hom-adjunction, which would not justify this pro-etale ringed-site application.

I also checked the change from abelian-group-valued sections in that model to A-module-valued sections in the global-Hom definition. They use the same source K-injective complexes and the same section differentials; forgetting A preserves the kernels and images defining cohomology. This is an identity of underlying complexes, not an unproved base-change assertion. Constant scalars act by postcomposition on Hom complexes. The model's naturality for a times the identity identifies the two A-actions, making the comparison A-linear. Its naturality descends to derived morphisms through localization, so it applies to each coprojection in step 4.

Step 4 contains only the explicit conjugation and the universal property of a direct sum. Its component formula is u mapped to iota_i[q] composed with u, exactly the map requested by the item. The isomorphism is therefore canonical as an A-module map, not merely an abstract group bijection. Each non-elementary ingredient is cited in the preceding steps and has a verbatim statement quotation in citations.json.

I tested the empty family (both sides zero), a singleton (identity comparison), the zero source, and negative q (the sections model is all-degree, with the target shifted by q). Torsion integral sources cause no scalar inversion in this argument. A family without a common lower bound never enters step 1. No stronger compactness or rational-coefficient conclusion is claimed. All proof steps are shorter than 2000 characters; none hides a separate comparison lemma. I checked delivery-errors B–E: no new elementary or duplicate nodes, no clause of the item repackaged as a new lemma, no definition cited in place of a theorem, no unchecked extra smallness or boundedness hypothesis, and no SGA source.

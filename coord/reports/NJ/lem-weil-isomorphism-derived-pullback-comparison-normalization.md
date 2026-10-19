# Stage-1 report: lem-weil-isomorphism-derived-pullback-comparison-normalization

## Files written

- `dag/nodes/sec-trace-formula/lem-weil-isomorphism-derived-pullback-comparison-normalization.json`: statement node, now split in nine steps. Mathlib verdict: no exact match or one-line specialization of the specified whole-cone normalization. The statement and existing statement dependencies are unchanged.
- `citations.json`: 25 verbatim statement quotations, one for every step/node citation.
- `searches.jsonl`: the actual Mathlib searches recorded by the authorized search command. The item preserves its inherited searches and appends these new results. Auxiliary preparation scripts remain in this sandbox only.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: this item is a child normalization prerequisite, not the unit's statement node.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint id, inverse-image/completion comparison terms, and the derived pullback sources. There is no project declaration stating all the ambient-complex, actual-unit, zero-shifted-coordinate and naturality clauses. The generic derived-pullback declarations use a different coefficient framework and do not identify this specified completed coefficient cone map. The upstream master source is reference material, not finished-proof evidence.

## Wanted literature

WANTED: none.

## Corrections and scope

The item was unsplit with an empty proof. No existing sandbox item or report existed to resume. I retained its statement, provenance, ancestral blueprint references, and inherited search history. Its source blueprint's assertion that automorphism pullback commutes with reductions is being made precise here for the ambient completed operation; I do not infer this operation is an equivalence on incomplete complexes.

The important extra work is identifying the actual unit of the simultaneous reduction/total-limit adjunction. Equality of all finite projections would not determine a map into a homotopy limit. Steps 2-3 instead compute the derived transpose of the identity, then identify it under the normalized strict Roos comparison. Likewise steps 5-7 compare both cone coordinates of the specified map. Naturality is proved on strict representatives and then localized, rather than asserted from evaluationwise identities.

No statement dispute was found. I did not change `def-weil-derived-complete` or infer a canonical lift merely from its existential Roos triangle. Step 9 invokes the existing `lem-weil-finite-free-completed-scalar-comparison`, whose L=E clause expressly states invertibility of the canonical zero-shifted-coordinate completion map for the item's complete objects.

## Blueprint, DAG and Mathlib searches

I read the chapter `sec-trace-formula`, unit `sk-thm-trace-transport`, and main-20261015 `prop-trf-rational-frobenius-integral-model.proof.md`, especially clauses (2)-(3). The item's ancestor is `thm-trf-l-function-euler-product`; this realizes the comparison prerequisite for its Step 1 (Global powers), through the two inherited intermediate nodes. The later composition identity is a separate statement and is not claimed here.

Whole-blueprint searches for `inverse-image comparison`, `completion unit`, `completion` and `Roos`, together with DAG searches for the item, strict augmentations, completion units and Tags 08TC/0941, located the existing comparison tools. In particular, `lem-weil-isomorphism-derived-pullback` gives an unspecified lambda only on bounded constructible inputs; `lem-weil-isomorphism-derived-pullback-reduction-tower` concerns coefficient reduction under inverse image, not the specified completed cone map. `lem-trf-integral-point-transport-tower-powers` has a related point-specific calculation, but is not used to prove this more general ambient statement. No new node is necessary.

The newly logged searches include two genuinely different LeanFinder phrasings, LeanSearch, Loogle and two source-grep patterns. LeanSearch's AdicCompletion hits concern ordinary module completion; I read `AdicCompletion.of_bijective` / `ofLinearEquiv` in `Mathlib/RingTheory/AdicCompletion/Basic.lean:647-672`. LeanFinder's `CochainComplex.mappingCone.mapHomologicalComplexIso` and variants are generic additive-functor comparisons; I read `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean:585-667`. The grep hit `isEquivalencePreservesLimits` in `Mathlib/CategoryTheory/Adjunction/Limits.lean:220-223` supplies only generic limit preservation, already covered by the existing DAG tools. None identifies the canonical completed pro-etale operation or its actual completion unit. The first Loogle query contained an unknown identifier and is recorded as an invalid pattern; the corrected query ran and had zero hits. No unavailable service is described as a negative mathematical result.

## Not duplicates

No new nodes were created. The split reuses the existing strict Roos, exact-product comparison, adjunction-calculus and scalar-comparison statements rather than creating specialized copies or restatements of the item.

## Review by NJ

I checked this split against delivery-errors B-E with the node statements and sources open. I read Stacks `derived.tex` Tag 08TC (`definition-derived-limit`), including its warning about nonunique isomorphisms and the ambiguity of maps into a homotopy limit. I read `sites-cohomology.tex` Tags 06YS (`lemma-K-flat-resolution`) and 0941 (`lemma-derived-limit-is-ok`), including its K-injective tower and ordinary-limit inclusion. I also read `sites-modules.tex` Tag 03D6 (`definition-pushforward`, which contains the tensor formula for module pullback) and its following adjunction lemma. In Bhatt-Scholze I read the discussion of completed tensor and derived completeness on pp. 22-25, particularly Definition 3.5.2 and Lemma 3.5.7(1). The blueprint and those references supply the route; the explicit normalization proof is marked agent-written because the sources do not state this exact comparison as a theorem. There are no new nodes requiring separate source checks.

Step 1 uses exactly the flat-term K-flat existence statement, the simultaneous derived-reduction model, the displayed definition of integral pullback, exact products on the pro-etale site, and the normalized strict Roos theorem. These provide one entire strict tower and its cone model. No Tor-amplitude, boundedness or constructibility assumption is inserted.

Step 2 uses the actual sequence ringed-site definition, the K-injective existence statement for small ringed sites, the derived-adjunction fraction formula, the stated canonical reduction/limit adjunction and the normalization of right-derived pushforward composition. I checked the adjoint orientation: simultaneous tensor reduction is left adjoint to limit after restriction. The transpose sends a tensor-unit generator x tensor 1 to its compatible components. For I K-injective in the varying-ring category and J K-injective in the constant-ring tower category, the composition theorem specifically gives the map lim(UI) to lim(J). This prevents an unjustified assumption that U preserves K-injectives.

Step 3 uses the strict Roos statement's precise zero shifted-product normalization. The chain map H(j U(a)) sends v_Q to (0,(j_n a_n r_n)_n), which is the inclusion of the representative from step 2. Thus this proves equality of the actual unit, not merely equality of its projections. This is a direct calculation from the cited normalizations, so it is marked elementary.

Step 4 uses all three relevant clauses of the pro-etale isomorphism inverse-image lemma: site reindexing, exact equivalence/limit preservation, and naturality of constant structure maps. The completed-module exactness and completed coefficient-projection square are explicitly in the comparison definition. The product action uses the same scalar transport on every factor; no inverse image for a general nonisomorphism is assumed to preserve products.

Step 5 uses that comparison definition's finite tensor-unit map, the sheaf tensor definition and the coefficient-reduction naturality statement. I wrote both multiplication inverse identities, the completed-scalar square, and the transition formula. These are balancing and reindexing identities, so no new node is justified. The isomorphism is of strict towers before taking a derived limit.

Step 6 uses the exact-product functor/strict-limit statement only after verifying all its hypotheses: both module categories are on small sites with exact countable products; G is additive and exact and its canonical product map is invertible. I checked its cone sign convention against the item's (b,a) coordinates. Both summands receive the same product comparison. The strict Roos theorem provides the same normalized total-limit identification. The resulting theta has the stated direction P_g N to G(hat N).

Step 7 uses the actual formula of comparison (b), not an unspecified lambda. The strict tensor-unit map is cancelled by multiplication on both tower/cone computations; the product comparison sends zero shifted coordinate to zero. With step 3 this gives theta kappa = G(u). This is a short calculation from cited statements and is marked elementary.

Step 8 uses the functorial strict derived-reduction statement, the integral operations' descent theorem, the exact-product comparison's derived naturality, and the definition of derived category as localization. I checked the tensor multiplication squares on chain maps and explained why they commute after inverting quasi-isomorphisms and composing roofs. These give resolution independence under the recorded comparisons. Naturality of kappa follows from its proven equality with theta inverse times the actual adjunction unit.

Step 9 uses exactly the scalar-comparison theorem's L=E clause, including the formula with zero shifted-product coordinate. Its input is any derived-complete ambient complex and its conclusion is invertibility of that actual map. No finite free model for N, boundedness or constructibility is required. Cancellation then yields the inverse in the order written in the item.

For small cases I checked N=0; g=id; a complex supported in one degree; and changes of the uniformizer exponent n in the transition equation. For g=id the multiplication and product comparisons become identities, so P_id N is hat N and kappa is the actual u_N. For a nonempty geometric point and N=R[1/varpi], all derived reductions vanish, so theta compares zero objects and kappa:N to 0 is not invertible; the statement correctly does not claim otherwise. For N=R or a finite free complete complex, the final inverse reduces to the canonical completion comparison. I also checked that multiplication works for arbitrary module terms, so it does not smuggle a flatness hypothesis into step 5.

All 25 citation quotations were checked as verbatim substrings of the statements actually used. The union of step uses equals proof_deps. Every proof dependency is in the unit's transitive route (including the generic derived-adjunction theorem in the Picard unit), so no off-route tool declaration is needed. No source prohibited by the no-SGA route lock is used. No statement-only node contains a hidden proof, because there are no new nodes. The nine steps are each below 2000 characters, and I checked them for hidden sublemmas: the non-elementary work is precisely in existing cited nodes, while balancing, transpose formulas and the two-coordinate cancellations are written out.

The preliminary server `review_split` returned PASS with 0 new nodes. The full dry run and push are performed after this report is written.

## Unfinished work

None within this one-level stage-1 split. Proofs of existing dependency nodes remain their owners' work. No Lean file or live project file was written, and no compiler, Lake command or build tool was run.

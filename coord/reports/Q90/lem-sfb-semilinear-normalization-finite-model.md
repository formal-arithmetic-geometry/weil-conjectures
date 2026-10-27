# Q90 stage-1 report: lem-sfb-semilinear-normalization-finite-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-normalization-finite-model.json: statement, split; no exact or one-line Mathlib match. Prescribed-field statement unchanged; six proof steps, all below 2000 characters. Added the existing fibre-product definition to statement dependencies because the statement uses the generic fibre.
- citations.json: one verbatim statement quotation for every step/node pair (10 pairs).
- No new nodes and no Mathlib leaves created. No unit or chapter files changed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for normalization/semilinear terminology. The smooth-base-change normalization-algebraically-closed-field theorem has different hypotheses and conclusions, and the generic relative Noether-normalization declarations concern another construction. No project declaration states every clause of this item.

## WANTED

WANTED: de Jong, Families of curves and alterations, 1997, Situation 5.3 and Lemma 5.6, printed pp.613--614, for lem-sfb-semilinear-normalization-finite-model. The filename in the inherited source record is absent in the read repository. No document was downloaded. The proof is therefore explicitly an agent assembly of the available Stacks sources and existing DAG statements, preserving the prescribed normalization route.

## Problems found and corrections

The imported item has a statement but no proof. Its upstream source pointer refers to a locally absent PDF and its blueprint ancestor is null. blueprint_refs.py ancestor confirms None; retained the inherited ancestry chain and precise from.place, and searched the entire blueprint for normalization, semilinear, finite separable, and normalization-extension. No blueprint node states the complete item. In particular the existing lem-sfb-semilinear-finite-normalization-model is a broader normalization/action ingredient but lacks dense-open etaleness. I did not cite it as a replacement proof or create a duplicate. The smaller existing finite-normalization-model-functoriality is used together with separate projectivity and generic-etale arguments.

There is no statement dispute: the prescribed extension need not be Galois, and the finite group may have a kernel on the scheme or constants. No faithfulness or invariant-open requirement was added. The normality of S is used to apply normalization-extends-cover on the chosen normal open. The affine base Spec k is essential for the global projective-space conclusion from finite-over-projective; I did not assume that a finite morphism over an arbitrary projective base has a global relative finite-projective-space embedding.

## Searches

All new item searches were executed with the required msearch.py command, and their results read. The command log is searches.jsonl. LeanFinder first returned relative normalization; the second phrasing returned galRestrict and galRestrict' and their compatibilities. Loogle returned the normalization API. LeanSearch was available and returned the same relative-normalization API. The grep returned Normalization.lean and ZariskisMainTheorem.lean. Read Mathlib/AlgebraicGeometry/Normalization.lean (construction and universal property) and RingTheory/IntegralClosure/IntegralRestrict.lean (galRestrict' assumptions, including fixed-base algebra morphisms). These do not specialize in one line to the whole semilinear model, its projectivity and its generic-etale conclusion. Existing searches inherited from Q50 are retained.

## Not duplicates

No new node is created. Whole-DAG searches located and reused finite-normalization-model-functoriality, finite-over-projective, the affine fraction-field and localization leaves, spread-finite-separable-extension, and normalization-extends-cover. The same-tag pair gate for new nodes is vacuous.

## Review by Q90

I read the worker brief, the three levels in SETUP.md, the stage-1 rules, GOAL.md, the item's chapter and unit, and delivery-errors B--E (including the historical duplicate). The route remains the equivariant normalization input beneath the direct-image alteration argument, not a change to that unit or its chapter. The item has no blueprint_update. No repair note exists and no earlier sandbox node or report was present.

For the item I read the available Stacks normalization construction and universal property (035H, 035I), restriction to opens (035K), normality (035L), and finite-normalization theorem (0AVK), the localization calculation (0307), the projective normalization proof (0GK4 and finite/projective composition), and the connected finite-etale normal-cover normalization comparison (0BQL). Also read the archived blueprint proof's primitive-element/discriminant paragraph used by spread-finite-separable-extension. The missing de Jong source is recorded above; no SGA source is used.

Step 1 uses exactly the finite-type/normal/integral/finite-surjective/function-field/Noetherian clauses of finite-normalization-model-functoriality. Its hypotheses hold for the specified S and M; it is about the actual normalization, not an unspecified alternative model. The other citation, finite-over-projective, says in its statement that the conclusion is global when its base is affine. I set that base to Spec k (Noetherian since a field has only two ideals), so no unmentioned relative projectivity theorem is used.

Step 2 uses the affine chart clause of def-fin-normalization-extension and the affine-function-field Mathlib leaf to place B in K. I read the statements of fibre-product-affine-spectra, localization-base-change, and integral-closure-commutes-localization: they give precisely the tensor-product fibre, its localization interpretation, and the localized closure in M. No unproved generic-etale assertion is taken from a definition. All localizations are inside the specified field M, and finite-dimensionality over K makes every element algebraic, hence integral over the field. Their structural maps give the canonical identification, not merely an abstract isomorphism.

Step 3 uses only spread-finite-separable-extension for a Noetherian domain B with fraction field K. Noetherianity comes from Step 1, and Step 2 provides the fraction field; separability and finiteness are assumptions of the item. Its statement supplies a domain D with the prescribed fraction field M and a finite etale map. The nonzero c makes its principal open contain the generic point. The local rings of that open are those of S, so it is normal; Spec D is nonempty irreducible and therefore connected. These are explicit elementary verifications of the comparison theorem's hypotheses, not hidden existence claims.

Step 4 cites normalization-extends-cover, whose statement says exactly that the normalization of the whole integral finite-type X in k(P) restricts to the supplied connected finite-etale cover of its nonempty normal open. This proves etaleness of our a over V because k(P) is the prescribed M as a K-extension. I checked the source comparison in Stacks 0BQL. I chose this existing node instead of creating a new generic-etale-normalization node or using a definition for normality ascent.

Step 5 cites the isomorphism/identity/composition and arbitrary compatible group-action clauses of finite-normalization-model-functoriality. Those clauses explicitly allow semilinearity and nonfaithful actions. I inverted sigma before taking Spec: h_j^*=sigma_j^{-1}|K. The pullback of b_j b_l is sigma_l^{-1} sigma_j^{-1}=sigma_{jl}^{-1}, so the lifts form the required left action. The final step is elementary evaluation of the inverse-pullback convention and of the composite structure morphism. No new equivariance or gluing lemma is smuggled into it.

For B--E: every cited node's statement was opened and used for its stated conclusion; citations.json copies those statements verbatim. There are no unsplit new nodes with concealed proofs, no duplicate or restated-clause nodes, no unsupported source-only citation, and no long proof step. The dependency closure (540 existing nodes for the initial citation set) does not reach this item. Off-unit non-Mathlib tools are explicitly justified in split_report.tool_uses; these are normalization/projectivity/spreading tools, not replacement alteration routes.

Edge cases: M=K gives the identity normalization because S is normal and the construction allows a nonempty etale open; dim S=0 gives Spec M over the finite field extension k(S)/k; nontrivial ker rho is permitted to act on M over K; a kernel acting trivially on M lifts trivially by uniqueness. No roots of unity, perfectness of k, Galoisness of M/K, or faithfulness is used. Without separability the dense-etale conclusion can fail (purely inseparable function-field extension), so that assumption is retained and used. Empty S is excluded by integrality/function field, and only nonempty affine charts are quantified over. All these cases agree with the stated conclusions.

## Unfinished work

None in the one-level split. Existing unsplit ingredients remain existing DAG items; they have not been silently treated as closed Lean proofs. Validation and direct-delivery command outcomes follow below.

## Validation

The first required deliver.py --no-push completed successfully: server preflight, check_dag and review_split passed at bcb2b220fa0. Corrected the report citation count from 11 to 10 after comparing it with citations.json; the split and citations were unchanged. A final dry run is run on this corrected report before the authorized direct push.

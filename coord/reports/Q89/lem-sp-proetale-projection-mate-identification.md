## Worker report

Item: lem-sp-proetale-projection-mate-identification. Group: Q89. Stage 1 only.

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-proetale-projection-mate-identification.json: statement unchanged, seven proof steps, status split, explicit generic tool uses, preserved inherited fields and searches, and actual newly logged searches appended.
- citations.json: 22 entries, one for every step/node citation, each checked as a verbatim substring of that node's statement.
- report.md: this report and signed mathematical review. The local write_split.py is only a sandbox drafting aid, not part of the delivery.

## New nodes

None. No Mathlib leaves created. The argument uses existing broader statements and writes the remaining action, balancing and adjunction calculations in the item itself.

## Attachments

None. The exact blueprint tag is absent from lean/WeilConjectures. Searches for the notions found the existing ExtendScalars/LowerStar.lean and ProjectionPullback.lean and the generic mate-transport modules. Their declarations define a mate and prove projection-related assertions, but do not state the identification with the literal inverse-image ring presentation and its normalized unbounded geometric adjunctions required here. They are not an exact attachment.

## Literature and blueprint

Read the smooth-purity chapter and sk-lem-sp-reduction unit records, and the current main-20261015 det-sp-reduction-direct-image proof. Its Step 1 fixes the counit-transpose map and its Step 4 composes those maps. This item identifies that same map with the ringed-topos coefficient mate before the cocycle is used; it does not replace the proper comparison or the unit's finite-window proof. The current item has no blueprint_update field.

Read sites-modules.tex Tag 03D3 (lemma-adjoint-push-pull-modules), including the module linearity criterion, and Tag 03EL (lemma-tensor-product-pullback), including its bilinear Hom calculation. Read sites-cohomology.tex Tags 07A6 (lemma-adjoint), 07A7 (remark-base-change), 0D6D (lemma-derived-pullback-composition), 0D6E (lemma-derived-pushforward-composition), 07A4 (lemma-pullback-tensor-product), and 0G7E (lemma-pullback-K-flat). Read derived.tex Tag 070I (lemma-K-injective), the adjacent K-injective computation statements, and the derived-adjunction discussion; the canonical pre-derived formula is stated explicitly in lem-pc-pre-derived-adjoint-functors-general. The new argument is marked agent-written because these sources supply general constructions rather than the project's particular presentation identification. WANTED: none.

Whole-blueprint searches for 'counit mate', 'constant coefficient', and 'inverse image tensor', and DAG searches by the relevant tags, titles and transport/K-flat concepts, found the cited existing tools. The ancestor command gives det-sp-reduction-direct-image. No imported blueprint node states the entire item in another form, so same_as remains empty. No node was created without searching: there are no new nodes.

## Mathlib searches

Read every result of the five searches in this sandbox's searches.jsonl: LeanFinder for the complete pro-etale mate identification; Loogle for CategoryTheory.mateEquiv and CategoryTheory.Adjunction; grep for conjugateEquiv_pullbackComp, mateEquiv_counit, derived counits; LeanSearch for derived tensor/ring-isomorphism and counit compatibility; and a second LeanFinder phrasing about pullback tensor comparison under ring presentation changes. All services answered successfully. Existing inherited search records are retained.

Read Mathlib/CategoryTheory/Adjunction/Mates.lean around lines 85-155: mateEquiv_counit gives the formal equation after adjunctions and the left comparison have been fixed. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean around lines 150-195: pullbackComp and conjugateEquiv_pullbackComp_inv concern ordinary module sheaf pullbacks. Neither establishes the canonical unbounded coefficient presentation and counit identification. The resulting whole-item verdict is no match; the formal inverse Hom calculation is written as an elementary final step rather than made into a new leaf.

## Errors and corrections

The statement is well-typed with the stated constant-ring transport and needs no correction. The item was unsplit with no proof, not an earlier completed sandbox attempt. The draft source reference initially called 0FND 'lemma-derived-adjoint-functors'; checking tags/tags corrected the label to lemma-pre-derived-adjoint-functors-general (the former is 09T5). No source or statement was changed.

## What remains

No mathematical clause is left unproved at this splitting level. Existing cited nodes retain their own stage status. No Lean was written or compiled. Server preflight and delivery results are recorded below when available.

## Review by Q89

I checked the item against the actual Tag 07A7 construction, not merely a generic claim that mates commute with transport. Its direction is T_Y G_A to G_B T_Z. Transposing under P_B gives a map P_B T_Y G_A to T_Z, so the counit identity in the item has the correct source and target. The ringed chi definition in lem-pur-ringed-coefficient-projection-cocycle uses the same direction. To instantiate that definition I used the composable chain A_Y to B_Y to B_Y with final map the identity; its cocycle conclusion is not used. This also avoids any dependency through the item's parent scalar-cocycle node.

For step 1 I opened def-weil-proetale-inverse-image and lem-pur-proetale-constant-coefficient-comparison. The former specifies c_R as the adjoint of the constant-section map rho_R; the latter says this exact map is an isomorphism for arbitrary schemes and rings. The coefficient square is then proved by taking adjuncts: both maps send a to the constant section phi(a). Invertibility alone would not have supplied that naturality square.

For step 2 I checked def-weil-pbc-proetale-operations against 03D3. Its statement includes the module Hom bijection and explicitly the map m tensor r to c_R inverse(r)m, not just the names of pullback and pushforward. I expanded that map and its inverse, verified the tensor balancing identities and restriction compatibility, and matched the direct-image scalar action with rho_R from def-weil-proetale-inverse-image. The sheafified tensor definition is given by def-pur-sheaf-tensor-product. Those elementary formulas identify the actual ordinary adjunction, including its evaluation counit.

For step 3 I checked the statements of lem-weil-pbc-ringed-projection-mate-exact and def-weil-pbc-proetale-operations. Both specify the canonical unbounded derived adjunction, with K-injective direct image, in the literal structural-map-equals-identity case. I did not infer equality of adjunctions merely from equality of functors. Exactness of inverse image gives Hom_K(L,u_*I)=Hom_K(u inverse L,I)=0 for acyclic L, so u_*I is K-injective. The statement of lem-weil-pbc-kinjective-hom-derived then identifies both derived Hom sets with the homotopy Hom sets. The representing-fraction equation in lem-pc-pre-derived-adjoint-functors-general reduces at identity representatives to the same ordinary adjunction. K-injective resolutions and its naturality extend that equality to every target. These citations supply precisely the facts used, including arbitrary unbounded targets and the chosen canonical normalization.

For step 4 I read the full compatibility formula of lem-weil-pbc-ring-sheaf-change-adjunction. It is stated for general ring sheaves on these pro-etale sites, not only constant rings and not only bounded below categories. I wrote out its specialization with identical base ring sheaves, source map c_R, and structural maps identity and c_R. Its compatibility hypothesis becomes c_R=c_R. Its r_U is restriction along this isomorphism, inverse to J_R. Taking t to be the new counit and its adjunct to be the identity verifies counit preservation under the supplied comparisons. This is the exact normalized derived transport needed, not a claim taken from its proof.

For step 5 I read the uniqueness and pure-section clauses of lem-pur-proetale-inverse-image-tensor-comparison, not only its existence of an isomorphism. I checked the coefficient balancing relation after c_A,c_B, using precisely step 1's square. I wrote the inverse coefficient transport and matched the resulting map on inverse images of x tensor b with the ordinary map in def-sp-reduction-direct-image-comparison. This proves equality of actual sheaf maps. It does not assume arbitrary global sections of a sheaf tensor are pure tensors: uniqueness of the cited comparison, and the sheafified tensor construction, are the justification.

For step 6 I checked that lem-pc-kflat-resolution supplies flat terms, as required by lem-weil-pbc-ringed-topos-kflat-pullback. That pullback theorem allows arbitrary structural ring maps, so it applies to identity-topos scalar change even when B is not flat over A. det-sp-scalar-extension-functor supplies the right B action and the K-flat scalar-extension formula; def-weil-pbc-proetale-operations supplies exact geometric inverse image. The statement of lem-weil-pbc-site-derived-tensor-descent gives an equivalence from the localization of flat-term K-flat complexes, so agreement on these representatives proves agreement on all derived objects and morphisms. No cohomology-by-cohomology replacement is used.

For step 7 I opened the actual chi defining formula in lem-pur-ringed-coefficient-projection-cocycle and the gamma definition in def-sp-reduction-direct-image-comparison. Substitution of the counit and lambda identifications gives the same transpose v_E. The explicit inverse function v maps to G_B(v) after eta_B proves uniqueness and equality without assuming gamma invertible. Naturality is inherited from the comparisons already proved natural, and the Hom bijection is natural. This last calculation is elementary adjunction algebra, not an uncited projection formula.

I tested the statement on q equal to the identity, phi equal to the identity, E=0, the empty source scheme, and the zero coefficient ring when permitted by the ring convention. The formulas reduce respectively to coefficient extension, tensor unitors, or the unique zero maps; no cancellation of a zero-ring scalar or nonzero section is used. I also checked the nonflat example A=Z/ell^2 to B=Z/ell: the proof uses a flat-term K-flat representative of E and its scalar extension, so it never replaces derived tensor by ordinary tensor on an arbitrary E and does not impose finite projective dimension on B. No boundedness or invertibility of ell on the schemes is used anywhere.

I checked B-E of delivery-errors.md against these files. There are no new nodes to be duplicates, disguised item clauses, or unsplit statements with proofs. All non-elementary tools are existing statements and are named in their precise steps; none is merely a definition of the fact needed. The proof-dependency union is exact, every quoted citation was checked verbatim, and the generic tools used in other units are declared only in split_report.tool_uses for the maintainer's judgement. I checked that the relevant cited tools do not depend on this item. Every proof step is below 2000 characters; each carries a single normalization or calculation. The only correction made during this self-review was the tag-label correction above. There was no separate second worker, as authorized by the direct-delivery brief.

## Validation

The required deliver.py --no-push process exited 0 with: `OK (not pushed) deliver/Q89/lem-sp-proetale-projection-mate-identification at 51b0dde6168: preflight passed`. All server preflight checks passed. The split creates zero new nodes and zero Mathlib leaves.

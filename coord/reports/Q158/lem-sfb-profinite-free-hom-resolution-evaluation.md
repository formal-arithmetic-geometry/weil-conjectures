## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-free-hom-resolution-evaluation.json — statement, split using existing nodes; not a Mathlib leaf.
- citations.json — thirteen step/node entries containing literal statement quotations.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searching the project library for the exact blueprint tag, profinite/free/internal-Hom language and resolution evaluation found no declaration giving this whole statement. The similarly named cohomology-resolution-evaluation-natural declaration concerns a different statement. Existing declarations in the module-object infrastructure are ingredients, not an attachment for this item.

WANTED: none. This is an agent-formulated argument supported by sources already present locally, rather than a claim that Stacks states the condensed specialization verbatim.

What was wrong: the node had no proof. Its source places the argument beneath paragraph (3) of constructible direct-image stability, but the blueprint paragraph itself only gives the larger open-direct-image route. I supplied the free-generator and resolution arguments and marked proof_origin.by as agent. The statement's doubled TeX backslashes were corrected to ordinary TeX; its mathematical meaning and all hypotheses are unchanged. The statement dependencies now explicitly name internal module Hom and the total right derived convention already used in the statement. No statement dispute was found.

The inherited blueprint ancestry is broken upstream: blueprint_refs.py ancestor reports None, following created.item through lem-sfb-admissible-direct-image. I retained the inherited null from.node and via chain and specified the precise source paragraph and purpose, rather than inventing a blueprint ancestor. The item is not the unit's key theorem, so no unit record is edited.

Nothing remains unfinished in this one-level split. All non-elementary ingredients are existing nodes. The broad existing profinite-free-functions-section-transport node is related but is not used as a substitute for the generator computation. The scheme-specific profinite-free-slice-derived-hom and module-object-ringed-site-derived-comparison nodes require a scheme and are not applied to the condensed point.

## Searches and reuse

I searched the whole DAG for Grothendieck module categories, free representable linearization, tensor/Hom adjunction, injective resolutions and the source tag 03EO; I also searched the blueprint with blueprint_refs.py for free module, internal hom and injective resolution. The matches are ingredients with different conclusions, not a duplicate of the complete item. No new nodes were needed.

Five actual msearch.py calls for Q158 and this item are preserved in searches.jsonl and appended verbatim (tool/query/result) to mathlib_searches: LeanFinder with the full product-evaluation/injective-resolution statement, Loogle with "ihomPoints", grep with ihomPoints|profiniteFree|internallyProjective in Condensed, LeanSearch with the free representable product/resolution question, and a second LeanFinder formulation using ringed-site linearization. All services responded. I read Mathlib/Condensed/Light/InternallyProjective.lean, especially ihomPoints and its naturality formulas, and Condensed/Solid.lean at profiniteFree. ihomPoints is for the light site and a constant abstract ring; profiniteFree constructs the module only. Neither states this arbitrary internal condensed-ring theorem or its resolution-normalized isomorphism. Generic resolution and freeYoneda APIs do not make the full item a one-line specialization. Earlier Q54 searches in the live item are retained as inherited history; I did not claim to have run them.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to compare. In particular the existing free-linearization-tensor statement is used directly for A[h_S] tensor A[h_P], and the existing ringed-site Grothendieck and K-injective nodes are reused instead of being restated.

## Review by Q158

I read the worker brief, stage-1 contract, GOAL.md, the three proof-route levels in SETUP.md, the item's chapter and unit records, the current blueprint direct-images proof, and both copies of delivery-errors.md B–E. The source paragraph (3) supports the role of this calculation in the open-direct-image route; it does not supply its proof. For the actual argument I read Stacks sites-modules.tex section-internal-hom, especially 03EO (lemma-internal-hom-adjoint-tensor), sites-cohomology.tex 07A5 (section-unbounded), derived.tex lemma-injective-resolutions-exist, 070J (lemma-bounded-below-injectives-K-injective), 070K (lemma-enough-K-injectives-implies), and 070Y (lemma-K-injective-defined), and injectives.tex 079H and 079P. No SGA source is used.

Step 1: I opened all five cited node statements. compact-hausdorff-surjection-quotient gives precisely quotient descent for the finite coproduct covering; I wrote the descent and continuity argument, including the empty object. ringed-site-grothendieck-abelian applies because the chosen skeleton is small and A_sec is a sheaf of commutative rings. internal-abelian-sheaf-module-equivalence leaves sections and restrictions unchanged. equivalence-preserves-limits supplies the transport of colimits and generators, and enough-injectives supplies each embedding in the explicit successive-cokernel construction. The construction is nonnegative, so no lower-bound adjustment or unspoken acyclicity hypothesis is needed.

Step 2: internal-section-tensor-comparison explicitly says E_A is exact and that its tensor comparison is the identity on pure tensors. sheaf-modules-tensor-closed explicitly states the natural adjunction with slice sheaf Hom. I gave the Hom-set argument identifying the transported right adjoint and its evaluation, instead of assuming that the equivalence definition alone proves this. Preservation of injectives is the elementary lifting argument through the exact inverse equivalence. Thus this step does not misuse the scheme-specific derived-comparison theorem.

Step 3: condensed-free-module-adjunction defines the adjunction including its generator unit. yoneda-hom-bijection states the evaluation-at-identity bijection and both naturalities; it is not merely a fully-faithfulness assertion. condensed-free-linearization-tensor states the tensor-to-product isomorphism and detection of maps by generalized generators. These statements give each displayed Hom bijection. I checked the inverse on every local pair (s,p), then checked the forward map on [pr_P] after pulling the section back along pr_S. This proves bijectivity, additivity and the A(S) scalar action as asserted, without claiming that sheafified free-module sections remain free.

Step 4: no external theorem is hidden. Substituting u composed with s, or v composed with p, into the formula of step 3 gives exactly the two asserted restriction operations. Naturality of a sheaf-module map gives naturality in N. The two product maps commute, which verifies mixed naturality rather than leaving it as an unexplained transport.

Step 5: grothendieck-k-injective applies to the actual internal module category proved Grothendieck in step 1. right-derived-functor explicitly states computation on every K-injective resolution and the compatible unit; bounded-below-injectives-kinjective applies to every given nonnegative I. Therefore J represents RH_P(M[0]) in the ordinary unbounded derived category. I do not require H_P(I) itself to be a complex of injectives and I do not identify ordinary H_P(M) with its derived object. I corrected an initial source-tag typo from 070D to 070J after checking the tag map.

Step 6: applying the already proved naturality to d_I and to a chain map gives the stated differential and resolution-map formula. Evaluating the degree-zero augmentation gives M(S times P) to I^0(S times P). This is an identification of complexes and their derived objects, not only of cohomology groups. No non-elementary fact is deferred to an uncited source here.

Small cases: P empty gives A[P]=0, H_P=0, and N(S times P)=N(empty)=0, since the empty family covers the empty object. P a point gives A[P]=A and H_P the identity. Empty S also gives zero sections. The zero ring yields only the zero module and satisfies every formula. For an arbitrary nonprojective profinite P the proof uses only the free adjunction and an injective resolution; it makes no higher-cohomology vanishing assertion. Arbitrary varying A is allowed, because multiplication on product sections is restricted along the first projection rather than assumed constant.

Against B1–B10: there are no new statement-only nodes, fabricated search records, missing leaf lines or duplicate blueprint imports; the single existing statement is self-contained with the two notation dependencies made explicit, and its TeX was normalized. Against C1–C8: all thirteen cited statements were read, their literal statements are in citations.json, no proof-only construction is imported, and off-unit generic tools are declared in split_report.tool_uses. I checked dependency reachability for the reused nontrivial nodes and found no path back to the item; the server check supplies the full graph validation. Against D1–D5: the actual free-generator argument is in the item and no clause is moved to a new node. Against E1–E7: smallness, coefficient variation, resolution bounds, product direction, the adjunction normalization and all compatibilities were checked explicitly. No source error or target-statement change is claimed. Every step is shorter than 2000 characters.

## Validation

The preliminary server review_split check passed with 0 new nodes. Its message that the constructibility unit has no realization yet is an existing unit-level condition; this item does not realize that unit's theorem. Final deliver.py --no-push and push results are recorded by the delivery tool.

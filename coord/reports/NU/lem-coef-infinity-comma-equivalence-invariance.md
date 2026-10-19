# Worker report: lem-coef-infinity-comma-equivalence-invariance

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-comma-equivalence-invariance.json: statement, split in eight steps; not a Mathlib leaf. The statement is unchanged. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement excerpt for each cited node in each proof step.
- searches.jsonl: five actual NU Mathlib searches, with their original service results. The item's six inherited NS search records remain intact in its JSON.
- report.md: this report and self-review.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item id and the oriented-fiber/comma-equivalence notions, including the CategoryTheory tree by quasicategory and comma terminology. No exact project declaration was found. The upstream master is reference material, not a proof certificate, and its corresponding terminology search gave no candidate either. The item's base record has no Lean audit or declaration to attach.

## WANTED

WANTED: archived Kerodon Remark 4.6.4.4, Tag 03PN, for lem-coef-infinity-comma-equivalence-invariance (online text read).
WANTED: archived Kerodon Definition 4.6.4.1, Tag 01KF, for the oriented-fiber-product convention of this item (this individual page and the subsection page timed out; the explicit convention is already in the item and its definition dependency).
WANTED: archived Kerodon Corollary 4.5.3.34, Tag 03PM, Corollaries 4.5.3.21 and 4.5.3.29, Tags 033L and 033T, and Corollary 4.4.5.3, Tag 01F3, for the supporting isofibration pullback and endpoint restriction arguments (online texts read).

No literature file was downloaded or modified. Because these sources are not archived in literature/, proof_origin.by is agent, with the online source identified explicitly. These are Kerodon tags; no Stacks theorem is substituted for the quasicategorical results.

## What was wrong and what changed

The item was a statement-only dependency created by NS, rather than an existing split. There was no sandbox node or report from an earlier attempt. I retained its statement, source, ancestry, metadata and previous searches. The bare reference to homotopy invariance needed the actual argument: the endpoint maps are isofibrations even though none of F,G,F',G' is assumed to be one. A strict pullback of an arbitrary equivalence need not preserve equivalences; the proof now states and checks the particular isofibration on the other leg at every application.

The split introduces no correction and no STATEMENT-DISPUTED. It does not identify an ordinary comma category with the coherent comma quasicategory. Mathlib Comma.isEquivalenceMap is only an ordinary-category result; it does not attach or make this node a Mathlib leaf. The inherited unit and blueprint ancestry serve the coefficient comparison in prop-coef-integral-exceptional-adjoint, proof paragraph 2. I read the current main-20261015 proof file there and the chapter/unit records. The present construction supplies the generic comma comparison below its existing marked-operadic restriction chain, without changing the unit route or replacing coefficient categories. There is no blueprint_update on this item or its ancestor.

## Existing nodes and Mathlib searches

Before choosing dependencies I searched the whole DAG by 03PN, 01KF, 03PM, oriented fiber, isofibration, categorical fibration and pullback terminology. tools/blueprint_refs.py searches for oriented fiber, isofibration, functor equivalence, categorical pullback, 03PM and 03PN all returned no matching blueprint node. Its ancestor command returned prop-coef-integral-exceptional-adjoint. The existing endpoint exponentiation, fixed-base pullback-equivalence, and change-of-base pullback-equivalence nodes supply all substantial inputs; no duplicate or elementary auxiliary node was created. All six cited nodes exist, are unmerged, and their dependency closures do not reach the present item. All statement lemmas used belong to this same unit; no off-unit proof tool is required.

I ran leanfinder in two genuinely different phrasings, loogle, grep and leansearch using msearch.py with this group/item. I read every returned signature. I also read the pinned source: Comma/Basic.lean:275-335, including isEquivalenceMap:311; Limits/Shapes/Pullback/Categorical/Basic.lean:346-365, including functorEquiv:354; CatCospanTransform.lean:30-82; CechNerve.lean:145-166; and Quasicategory/Basic.lean:32-92. Ordinary comma/categorical-pullback and Cech adjunction facts do not give the desired statement for arbitrary quasicategories. The second semantic search returned two-truncated homotopy-category and left/right homotopy lemmas, which do not state coherent comma invariance. The model-category closure hits require the Joyal comparison input and do not themselves give this item. Hence there is no exact or one-line Mathlib match. No service was unavailable in these five searches.

## Not duplicates

No new nodes. In particular I reuse lem-coef-infinity-isofibration-base-change rather than create a general pullback-invariance node carrying its same Kerodon tag.

## Review by NU

I read Kerodon 03PN online: it applies 03PM to the arrow-category cospan, exactly the cospan used here. I read 03PM and its two cited corollaries 033L and 033T. The latter requires an isofibration for the strict-to-homotopy-pullback comparison; this is why the endpoint restriction hypothesis is proved rather than assumed for F or G. I read 01F3, which asserts that restriction along any simplicial subset is an isofibration between quasicategories. I also checked the online pointwise-equivalence statement 01DK, but do not need to cite it: Step 3 preserves the actual inverse triangles by a specified simplicial evaluation action. The item and its source agree for arbitrary strictly commuting cospans of equivalences. No ordinary-category approximation is used.

For Step 1 I opened def-cbc-enhanced-diagrams-cones and lem-coef-infinity-isofibration-exponentiation. The former explicitly defines degreewise products/pullbacks, the internal Fun simplicial set, inner horns, and quasicategories; the latter expressly states that restriction Fun(B,C) to Fun(A,C) is an isofibration for any degreewise inclusion. Taking the two endpoints gives precisely p and p', not either F or G. I checked that the boundary simplex is a disjoint pair of vertices, and wrote the conditional horn lifting for T and T' explicitly. There is no claim that an unrestricted strict pullback of quasicategories is always a quasicategory.

For Step 2 the definition dependency gives exactly the quasi-inverse and two coherent natural equivalences required by the conclusion. The inverse for each product is the product of the given inverses. Both inverse-edge and inverse-triangle witnesses are coordinatewise, so no product-preservation theorem is hidden here. For Step 3 the same definition supplies internal Fun and the inverse-triangle convention, while exponentiation supplies quasicategory status of the relevant functor objects. I wrote the simplicial evaluation action Phi_K and checked its restriction maps. Applying it to the given unit/counit and their inverse witnesses proves equivalence of the arrow-category map directly. This is a definition-level construction, not an uncited rectification or pointwise recognition theorem.

For Step 4 I opened lem-coef-infinity-isofibration-pullback-equivalence. Its statement permits an arbitrary functor equivalence y and an isofibration on the other leg, with no lifting hypothesis on y; substitution (P,P',A',H,p') therefore gives exactly q:S to A'. The statements of lem-coef-joyal-quasicategory-characterizations and lem-coef-joyal-model-structure explicitly identify coherent functor equivalences with Joyal weak equivalences and supply two-out-of-three. They justify j from the exact equation qj=u, with its source and target both known quasicategories. No full-faithfulness statement is taken from a definition node.

For Step 5 I checked the same characterization's fibration clause and the model-structure statement's right lifting characterization. The prescribed base coordinate paired with the lifted A' coordinate proves that rho is a pullback fibration. Both endpoints are quasicategories, so the characterization converts back to an isofibration. I opened lem-coef-infinity-isofibration-base-change: it specifically requires BOTH structure maps p and rho to be isofibrations, and an equivalence j strictly over their common base P. These are all established before applying it, and its arbitrary test functor is exactly a:X to P. Its statement also supplies U's quasicategory status. This differs from the change-of-base input of Step 4, so neither citation is being used for an unasserted stronger result.

For Step 6 I checked the same lifting-characterization clauses for tau. The filler is paired with the prescribed X' simplex, and both endpoint objects T',X' were proved quasicategories in Step 1. This is an explicit elementary lifting-square argument. For Step 7 I reopened the change-of-base node: now the equivalence is V:X to X' and the isofibration is tau:T' to X'. I wrote the simplex bijection identifying its actual pullback with U in both directions, checked the equation p'(eta')=Ha(x)=a'V(x), and checked that both substitutions commute with every simplicial operator. Thus its conclusion is the stated beta, not just an unspecified equivalence of categories.

For Step 8 the two Joyal statements provide composition closure through two-out-of-three and its converse characterization on quasicategories. The coordinate formula for beta alpha is literally the requested formula in each degree. Both endpoint equations follow by taking coordinates, so no coherent equality is substituted for the required strict equality. I checked D=D'=Delta^0 with w the identity and G'=hG: no step asks that the chosen object be in the image of F.

Small cases checked: C or D empty, B empty (forcing C,D empty whenever F,G exist), all categories points, discrete quasicategories, and nerves of ordinary categories. Empty products/pullbacks are permitted by the definitions and by the change-of-base node's explicit no-nonemptiness clause; the fixed-base node has no nonemptiness condition either. For a discrete B with F and G selecting distinct objects, T is empty and its primed counterpart is empty under the specified equivalences. In a nerve with a noninvertible arrow b0 to b1, F selecting b0 and G selecting b1 gives a nonempty comma category although b1 is outside the image of F. This tests the final clause against the tempting but invalid image restriction. No statements about Kan fibrations of spaces or ordinary category equivalences are substituted for the quasicategorical assertions.

I checked delivery-errors B--E against the actual files. There are no unsplit new statements, no hidden hypothesis additions, no clause-restatement nodes and no source-route substitution. Every cited statement is quoted verbatim in citations.json, proof_deps is the exact union of uses, and statement dependencies still contain the explicit definition node. The longest proof step is 1390 characters, so none crosses the 2000-character review threshold; I also checked that the only intermediate constructions are direct evaluation and degreewise pullback identifications or explicit applications of the cited lemmas. Nothing was sent to another worker: this is the direct-delivery self-review required by the brief.

## Unfinished work

None in this split. Foundational lemmas remain the existing DAG nodes; no proof is silently moved to a new node. Only the requested literature archives remain WANTED. Validation and push are performed by the mandatory delivery tool after this report is written.

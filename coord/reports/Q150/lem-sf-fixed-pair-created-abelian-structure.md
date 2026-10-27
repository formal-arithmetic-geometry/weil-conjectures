# Q150: lem-sf-fixed-pair-created-abelian-structure

## Files written

- dag/nodes/sec-six-functors/lem-sf-fixed-pair-created-abelian-structure.json — statement, split; no complete Mathlib match. The imported statement is verbatim unchanged.
- citations.json — one verbatim statement quotation for every citation in every proof step.
- report.md and searches.jsonl — report and actual searches for this item.

No new nodes and no new Mathlib leaves. The existing Mathlib leaf lem-galois-equivalence-preserves-limits is reused. The sandbox initially had only dispatcher brief markers; no previous split, report, or search results existed to resume. write_split.py is a sandbox-only drafting helper, not a delivery file.

## Attachments

None. I searched the whole WeilConjectures tree for the exact blueprint tag and for fixed-pair/IsoAlgebra declarations, then read the actual foundational sources. IsoAlgebra.abelian and its additive/finite-preservation instances cover only part of this item's clauses. The project Endofunctor/Algebra.lean also constructs limits for ordinary algebras and proves closure of invertible structures; these are ingredients, not one declaration (or a collection of clause statements) stating all this item's creation, cancellation, and exactness clauses. In particular no exact item attachment was found. Mathlib's Algebra.forget_reflects_iso is likewise an ingredient, not a project attachment.

## WANTED

None. All sources needed here are available. No SGA source is used.

## Corrections and scope

The initial node had no proof. I retained its statement, creation data, inherited blueprint provenance and all inherited Mathlib searches. I corrected the source place's stale Endofunctor/IsoAlgebra.lean shorthand: the all-diagram construction and closure results are in lean/WeilConjectures/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:420-669; finite exactness and abelianness are in Mathlib/CategoryTheory/Preadditive/EndoFunctor.lean:64-143. The similarly named CategoryTheory/Endofunctor/IsoAlgebra.lean concerns transport and Grothendieck structure and is not the source of arbitrary created limits.

There is no statement dispute or change of unit route. blueprint_refs ancestor returns None, matching the inherited null ancestor and its two-node via chain. The item supplies the categorical input extracted from parent proof steps 1-2 for six-operations package clause (2). I read dag/chapters/sec-six-functors.json and dag/units/sk-thm-sf-package.json. Neither is changed and this item is not the unit's key theorem.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches for fixed pairs, fixed-pair, and kernel/cokernel statements were read. new-p6-etale-weil-abelian is a specialized lisse-Weil assertion, not a replacement for this general complete/cocomplete-category theorem. lem-galois-equivalence-preserves-limits already supplies the sole non-elementary external theorem required here. The existing fixed-pair category definition and abelian-category definition are reused verbatim. The universal-property calculations are proof steps, not new nodes restating individual clauses of the item.

## Mathlib search assessment

I ran msearch.py with two semantic phrasings for the complete theorem (leanfinder), one leansearch query, Loogle for IsoAlgebra, and a grep for IsoAlgebra/IsIsoStr/forgetCreatesLimits. Their actual results are in searches.jsonl and appended to the item's inherited searches. All services answered. I read the relevant hits: Mathlib's Endofunctor.Algebra permits arbitrary structure maps; its forget_reflects_iso is at Algebra.lean:140. CategoryTheory.Preadditive.EndoFunctor.lean:34 and :68 supply algebra preadditivity and additive forgetting. Monad/Limits.lean constructs limits of Eilenberg-Moore algebras, which is not this fixed-pair category. Abelian.Transfer.lean transfers along an equivalence/adjunction, and U here is not asserted to be an equivalence. Thus none states the whole item. The exact equivalence-preservation declarations were read in CategoryTheory/Adjunction/Limits.lean:106 and :220 and are already recorded in the cited existing leaf. The second phrasing returned the coimage-image criterion; I deliberately proved the normal-mono/normal-epi axioms directly, so no uncited use of that criterion remains.

## Review by Q150

I read delivery-errors B-E in full, the stage-1 brief, the stage document, GOAL, the three levels in SETUP, the worker role and tools documentation. I checked the actual sources with the node statements open: the fixed-pair definition gives exactly the equation f theta_X = theta_Y T(f) and faithful forgetting; def-sp-abelian gives preadditivity, zero objects, finite biproducts, kernels/cokernels, and normal monos/epis. The equivalence-preservation leaf states preservation of ALL limits and colimits, with no finiteness restriction. Its Stacks source is Tag 0038, categories-lemma-adjoint-exact, which I read in categories.tex:3472ff. I also read homology.tex at Tag 0109 (definition-abelian-category) and Tag 010E (definition-exact); I use the cited node's normal-mono/normal-epi convention to prove abelianness, and Tag 010E only to spell out the meaning of exactness, not as an uncited theorem.

Step 1 uses def-sp-abelian for ambient abelian morphism groups and bilinear composition and the fixed-pair definition for the commuting square. I checked closure under addition, negatives, and zero using the stated additivity of T, and smallness as a subset. Step 2 uses only the fixed-pair equation and writes the inverse equation by multiplying on the two sides; this is valid even before B has any abelian structure.

Step 3 uses the fixed-pair definition and the equivalence-preservation leaf. T is an autoequivalence as required, all indexing categories are V-small, and the ambient (co)limits exist by hypothesis. I checked that both the theta and inverse-theta families satisfy the cone identities. The two factorizations alpha and beta have correct source and target; testing their composites with p_i and T(p_i) proves inverse identities. This establishes the precise canonical comparison formula rather than merely asserting that structure transports. Step 4 uses the fixed-pair definition: testing a zeta = alpha T(a) after every projection proves that the actual universal map is a commuting morphism. Uniqueness of structure and reflection of arbitrary limiting cones are included, so the proof establishes creation and preservation, not just existence.

Step 5 uses exactly the same two cited statements, now with colimits. The displayed equations gamma T(j_i) = j_i theta_i and delta j_i = T(j_i) theta_i^{-1} have the correct variance. Both inverse identities follow by testing on the two colimit families. Step 6 uses the fixed-pair definition, and the equivariance of the universal descent is tested after T(j_i), whose joint uniqueness is justified by T preserving this colimit. This is where merely using the original j_i would be a type error; the final proof has the correct family. Uniqueness of the lifted structure and reflection of colimiting cocones are proved explicitly.

Step 7 uses the two definitions and the already proved steps. I checked empty diagrams separately, the unique commuting map between underlying zero objects, and the two binary-product injections by testing their squares with each projection. The biproduct identities imply the coproduct universal map b_1 p_1 + b_2 p_2 directly. Kernels and cokernels are the parallel-pair constructions against zero, so their underlying cones/cocones have precisely the ambient universal properties. No abstract biproduct or exact-functor theorem is taken without proof.

Step 8 uses those definitions and created kernels/cokernels. Faithfulness immediately reflects mono and epi, but does not by itself preserve them. I checked the other directions independently: monicity in B forces its kernel map to be zero, and every ambient difference killed by Uf factors through that map; the cokernel/difference argument is the dual. This avoids assuming the desired abelian structure prematurely.

Step 9 uses the normal-mono clause of def-sp-abelian in A, after step 8 has proved Uf monic. Its auxiliary target Z need not be a fixed pair. The ambient witness b factors through the CREATED cokernel q, proving that Uf is already a kernel of Uq; I then checked the unique factorization commutes by cancellation against Uf. Step 10 uses the normal-epi clause, with an auxiliary source Z that likewise need not lift. The factorization through the created kernel gives the cokernel universal property. For the equivariance calculation I checked cancellation against T(f): it is epic because T(f) = theta_Y^{-1} f theta_X, not because an unstated preservation theorem is assumed. All the axioms of the cited abelian definition have now been supplied.

Step 11 uses the two definitions and the previous constructions. I corrected the draft to write WHY g kills the image: g = b q by the cokernel property, so g kills ker(q). Thus the comparison t from image(f) to kernel(g) is an actual kernel lift, not a presumed identification. U preserves both objects and this comparison by their proved universal properties. Exactness is invertibility of this inclusion, and step 2 detects it. Faithfulness also detects the zero composites. Applying this at each term covers finite and arbitrary sequences and short exact end terms. No generic theorem that exact faithful functors reflect exactness is silently invoked.

All citations.json quotes are verbatim complete statements read from the three cited nodes; the citations use their statements, never facts only inside their proofs. The proof is agent-written with exact source places. Every substantive universal-property step is conservatively marked non-elementary; the only external non-elementary fact used without reproving it is the cited equivalence-preservation lemma. The other steps carry their calculations in full rather than hiding new standard lemmas. There is no new unsplit statement to require separate hypothesis tests. Every step is shorter than 2000 characters (maximum 1088 in the first draft), so there are no long steps hiding comparisons.

For small cases I checked the zero category; empty limits and colimits; the zero morphism and identity morphism; and A = Ab with T = id. In the last case objects are abelian groups with an arbitrary automorphism, equivalently modules for Z[t,t^{-1}], so B is not silently identified with A and no finite-order condition on theta appears. The constructions give coordinatewise products, quotient coproducts, invariant kernels and quotient cokernels. No Grothendieck hypothesis, generator, enough injectives, or smallness of the entire object class is used. The only smallness restriction on diagrams is precisely the V-small one in the statement.

## Unfinished work

None in the split. The required first dry run completed successfully and wrote the durable receipt .stage1-ready.json. Final report validation and push follow.

## Validation

The first deliver.py --no-push completed and saved its successful server-preflight receipt at 44cdcbfd1e2. The unchanged statement, exact union of proof dependencies, all 19 verbatim citation quotes, and step lengths were independently checked in the sandbox. No Lean was written or compiled. The final report is validated again before the direct-delivery push.

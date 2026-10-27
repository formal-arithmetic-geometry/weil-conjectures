## Worker report

Q133, stage 1, 2026-10-22. Item: lem-pur-etale-residue-direct-image-tor-window.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-residue-direct-image-tor-window.json: existing statement node, now split into five steps; not a Mathlib leaf. Statement and statement dependencies retained verbatim.
- citations.json: one entry per step/node pair, quoting the cited statement verbatim, including the relevant hypotheses.
- searches.jsonl: actual msearch.py output records for this item.
- report.md: this report and signed review.

## New nodes

None. Zero new nodes and zero Mathlib leaves. In particular the supplied-bound projection formula, the bounded-heart amplitude lemma and the ordinary etale residue test all already have nodes; none has been copied into a new node.

## Attachments

None for the item. Searched lean/WeilConjectures by its exact blueprint tag and by residue/direct-image/Tor concepts. Read WeilConjectures/SixFunctors/Etale/Derived/DirectImageTorAmplitude.lean and Finiteness/ResidueTorTest.lean. The former's torAmplitudeIn_rightDerivedLowerStar_of_finite requires finite-type schemes over a field and uses the specific bound 2d. It does not state the arbitrary-morphism, supplied-bound item. The latter supplies a residue criterion, not the direct-image conclusion. Neither is an attachment for this item. The proved triangulated and plus/total comparison declarations are used through their existing DAG nodes.

## WANTED

None. The coefficient arithmetic is not re-proved, and the finite-presentation argument uses the explicit presentation of A/(t), so no missing local-fields reference is needed.

## What changed and why

The original item was statement-only. Its statement is true as written. Bhatt–Scholze Lemma 6.7.17 was read in the local PDF (printed page 57). It has quasi-excellent, ell-coprime, finitely presented geometry and is not directly applied to this arbitrary scheme morphism. The proof_origin is therefore agent: it extracts the residue-projection strategy using existing DAG theorems with exactly the abstract supplied-bound hypotheses. The additional source read is Stacks derived.tex: 015A, definition-higher-derived-functors; 05TC, lemma-negative-vanishing; and 08J5, remark-truncation-distinguished-triangle. In particular, finite Postnikov induction replaces any proposed convergence assertion on an unbounded double complex.

No statement dispute or weakened statement is involved. The assumed bounded constructibility of F is kept and is checked precisely when the existing residue-test node is applied. No finite-type, separatedness, base-field, invertibility-on-X, or absolute field cohomological-dimension hypothesis is inserted. The relative bound applies to all A-module sheaves, as required by the projection lemma.

## Blueprint and existing-node searches

Read the chapter and transport unit records and the current main-20261015 transport unit and coefficient-reduction exceptional proof. The item has no imported blueprint ancestor: blueprint_refs.py ancestor prints None. Kept that provenance and its existing place, which traces the finite-stage prerequisite through the parent coefficient lemma to thm-pur-rational-and-qbar-purity Steps 1–2. The current parent uses this item in its Step 3.

Ran whole-blueprint searches for “Tor amplitude”, “cohomological dimension”, “residue”, and “projection-finite-constant”; searched the entire DAG by ids and statements for residue/Tor, bounded-heart amplitude, hypercohomology, finite rectangles and direct-image bounds. Opened the existing statements before choosing them. thm-sf-direct-image-tor-amplitude and lem-sf-direct-image-tor-amplitude-noetherian impose geometric hypotheses unavailable here; they are not substitutes. lem-exc-residue-tor-test, unlike its pro-etale analogue, is exactly on the ordinary etale site and has the coefficient and constructibility hypotheses available here.

The new msearch.py calls comprise LeanSearch, Loogle, grep and two distinct LeanFinder phrasings, all logged. Read the returned types: the Tor hits are ordinary categorical Tor; sheaf-pushforward hits are underived; IsGE/IsLE and bounded-representative hits give cohomological support, not preservation of Tor amplitude under arbitrary supplied-bound etale direct image. No exact or one-line generalized Mathlib match was found. Existing search records on the item were retained.

## Tool uses

split_report.tool_uses declares generic tools from other units, with the reason for each. They supply ordinary module-sheaf category properties, derived heart comparison/negative vanishing, finite Postnikov induction, finite-constant projection and residue detection. These are the coefficient argument's prerequisites; they do not replace the transport unit's geometric purity route. No maintainer-owned top-level tool_uses field is written. The two closed source-library nodes for triangulatedness and plus/total comparison are also cited explicitly.

## Review by Q133

I read the item and parent statements against the local Bhatt–Scholze Lemma 6.7.17, distinguishing the paper's geometric hypotheses from this item's supplied relative bound. I also read the Stacks truncation triangles (08J5), negative-vanishing proof (05TC) and higher-derived-functor definition (015A). For the generic derived-functor comparisons I opened the source-library Triangulated.lean instances and PlusCompatibility.lean, including the isomorphism between bounded-below and total derivation. No new node is proposed, so there is no new statement to leave without a source, definition dependency or search.

Step 1 uses def-kun-tor-amplitude for the two permitted degree-zero test sheaves, lem-kun-tensor-unit for the unit isomorphism, and def-sc-finitely-presented-module for the presentation criterion. The quotient presentation A --t--> A --> A/(t) --> 0 is exact at the last two terms; injectivity of multiplication by t is neither asserted nor required. This is elementary even for n>1, when that multiplication is generally not injective. Boundedness of K follows from the unit test, and L=K tensor^L kappa is bounded by the other test, without asserting flatness of kappa.

Step 2 uses the statement, not the proof, of lem-sf-projection-finite-constant. I checked its ring is Noetherian, its input is D-minus, its coefficient module need only be finitely presented, and its higher-image bound concerns every module sheaf. Those are precisely the present hypotheses and Step 1's consequences. The asserted output is an isomorphism in D(Y_et,A), so no per-degree replacement or coefficient-category identification is hidden here.

Step 3 cites lem-weil-pbc-module-sheaves-grothendieck-abelian for both source and target categories, lem-weil-pbc-module-sheaves-enough-injectives and prop-weil-pbc-kinjective-resolutions-exist for the source resolutions, and lem-weil-pbc-module-direct-image-left-exact for additivity and left exactness. The statement of lem-pc-right-derived-functor-triangulated gives both preservation of triangles and commutation with shifts. lem-sp-derived-functor-single-identification says precisely that the degree-zero object's nonnegative derived cohomology is the classical R^q functor; src-right-derived-functor-plus-compatibility then moves that statement to the unbounded functor used by projection. Finally lem-weil-pbc-derived-functor-negative-vanishing applies to the bounded-below single sheaf and gives the negative half of [0,c]. Thus this step does not accidentally assume a higher-image bound for the wrong coefficient category or invoke a definition as though it were a theorem.

Step 4 uses exactly lem-pur-bounded-heart-amplitude with the class of all source module sheaves, which is closed under isomorphism and contains zero, with heart interval [0,c]. Its hypotheses c>=0 and a<=b are assumed in the item. The input L has cohomology in [a,b] by Step 1. The lemma therefore produces [a+0,b+c]. It makes no product or completeness assumption and no assumption of constructibility of L, which is useful because none was silently obtained here.

Step 5 uses the derived isomorphism already obtained and the bound from Step 4, then invokes the exact statement of lem-exc-residue-tor-test with T=Y and F. Its coefficient quotient and residue are identical, and its bounded-constructible hypothesis on F is explicitly supplied by the item. Its conclusion is the universal Tor interval, not only a constant-sheaf test; def-kun-tor-amplitude states the claimed vanishing for every possibly nonconstant N. This is why the residue-test citation is essential.

I tested n=1 (the residue is A and the projection is the unit case), n>1 (the nonflat residue is still finitely presented), c=0, a=b including negative shifts, K=0 and the empty scheme. All intervals and coefficient comparisons remain valid. The proof never infers flatness from boundedness, never imposes a field cohomological-dimension bound, and never replaces ordinary etale coefficients with completed or condensed ones. Each step is below 2000 characters; the entire five-step proof text is below 3000 characters. The citations file includes every uses entry and quotes only actual node statements. No steps are clauses moved into fresh nodes. No unresolved mathematical issue remains.

## Unfinished work

None in the requested stage-1 split. Downstream proof obligations are the already existing nodes, not unreported claims.

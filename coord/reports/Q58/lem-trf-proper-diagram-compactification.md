# Stage-1 report: lem-trf-proper-diagram-compactification

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-diagram-compactification.json`: repaired statement split with five proof steps and no new nodes.
- `citations.json`: verbatim statement quotes for every node used by every step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its geometric phrases, and the imported blueprint tag; no sorry-free project declaration states this theorem exactly.

## WANTED

None.

## What was wrong and what changed

The returned version independently compactified the two proper legs, used the common-modification node without a common open, and claimed that arbitrary graph closures projected isomorphically onto their chosen first factors. Those claims do not follow and the standard rational-map blow-up is a counterexample to the projection assertion. I removed the graph and common-modification citations and did not replace the already chosen compactifications by a later tuple closure.

The repaired proof follows the required order. It first fixes (Y^*) and auxiliary compactifications (B',X',C'). It forms (B^*) as the scheme-theoretic image of (B\to B'\times Y^*\times Y^*), so the two projections are global (b_i^*). It then forms (X^*) as the image of (X\to X'\times Y^*), and (C^*) as the image of (C\to C'\times B^*\times X^*\times X^*), so (p^*,q^*,c_i^*) are global projections from the outset. The inverse-image assertions use restriction of scheme-theoretic images to the opens (X'\times Y\) and (C'\times B). For each proper leg, the restricted tuple is an immersion; the proper-image statement gives a proper image and a surjective factor, while the closure statement makes that factor an open immersion, hence an isomorphism. Proper-immersion and separated-cancellation statements are cited at the corresponding properness/closed-immersion checks. The former unsupported Cartesian assertions and the invalid tuple replacement are therefore gone.

## Review by Q58

I read Varshavsky, *Lefschetz–Verdier trace formula*, Remark 1.1.3 (PDF p. 7) and §4.1.4(a), final paragraph (PDF p. 27). The item statement is unchanged and retains the source's separated finite-type schemes, two proper legs, four arbitrary correspondence maps, commuting equations, dense open compactifications, and the two specified Cartesian restriction squares. Varshavsky supplies the tuple-closure construction; the Cartesian clauses are verified here from the existing scheme-theoretic-image lemmas, as required by the return review.

For Step 1 I read `sk-thm-nagata-compactification`: over the qcqs base (S=\operatorname{Spec}k), every separated finite-type morphism has a dense compactification. This supplies (Y^*) and the auxiliary (B',X',C'), with no claim that these auxiliaries are the final compactifications.

For Step 2 I read `sk-lem-nagata-sketch-closure`. Its statement gives a closed scheme-theoretic image, an open immersion of the source into that image, and scheme-theoretic density; those are exactly the facts used to define (B^*), (u_B), and the projection maps (b_i^*). Properness of (B^*) is the elementary closed-subscheme-of-a-proper-product argument. The tuple map is an immersion because the (Y^*\)-valued graph is closed and (j_B) is open; no graph projection is asserted to be an isomorphism.

For Step 3 I checked all hypotheses of `lem-weil-pbc-scheme-theoretic-image-proper` (Stacks Morphisms Lemma 0AH6): the target projection (X'\times Y\to Y) is separated and locally of finite type, and its composite with the restricted tuple is the proper map (p). The cited statement says that the scheme-theoretic image is proper over (Y) and that the factor from (X) is surjective. `sk-lem-nagata-sketch-closure` says the same factor is an open immersion, so it is an isomorphism. `lem-weil-pbc-separated-cancellation` supplies separatedness of the immersion, and after the image identification `lem-weil-pbc-proper-immersion-closed` (Stacks Schemes 01IQ/Morphisms 01U2) confirms the proper immersion is a closed immersion. I then applied `lemma-nagata-scheme-image-restrict-open` to (h_X:X\to X'\times Y^*) with the open (X'\times Y); its conclusion is precisely (X^*\times_{Y^*}Y\cong X). This checks the open, quasi-compact, and quasi-separated hypotheses rather than importing the old graph lemma's unrelated assertion.

For Step 4 I repeated that exact check for (h_C:C\to C'\times B^*\times X^*\times X^*), restricting to (C'\times B\times X^*\times X^*). The composite to (B) is (q), so the proper-image hypothesis is met; the closure factor is simultaneously open and surjective, and the proper-immersion and separated-cancellation statements apply as in Step 3. Restriction of scheme-theoretic image gives (C^*\times_{B^*}B\cong C). The projections define (q^*) and both (c_i^*) before any density argument, and the product projection makes (q^*) proper.

For Step 5 I read the uniqueness clause of `sk-lem-nagata-sketch-closure`: maps to a separated target that agree on a scheme-theoretically dense open agree everywhere. The two maps (b_i^*q^*) and (p^*c_i^*) agree on (C) by the original equation (b_iq=pc_i), hence agree on (C^*). The definition node `def-weil-pbc-cartesian-square` says that the two canonical isomorphisms just proved are exactly the requested Cartesian squares. Properness and finite type of all closures follow from closed subschemes of products of proper finite-type (k)-schemes; no original scheme was assumed proper and no original leg square was used.

I checked small cases while revising: if a leg is already proper, its auxiliary compactification can be the leg's source and the image construction reproduces the usual graph closure; for an empty source, the scheme-theoretic image and the dense-open assertions are vacuous in the stated sense; and the rational map ((x,y)\mapsto[x:y]) confirms why the old fixed-first-factor graph closure cannot define a global map. The repaired steps are each below 2000 characters and contain no hidden long lemma. The DAG dry run `srvcheck.py ... check_dag` passed after the node and citations repair.

## Not duplicates

No new nodes were created, so there are no duplicate pairs.

## What could not be finished

Nothing remains for this split; the required final delivery dry run and push are next.

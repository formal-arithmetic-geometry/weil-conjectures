# Stage-1 split: lem-sc-glue-component-reduced-cover-sections

## Files written

- dag/nodes/sec-curve-estimates/lem-sc-glue-component-reduced-cover-sections.json: split the item in three steps; no new nodes or Mathlib leaves.
- citations.json: verbatim statement excerpts for all seven step citations.

## Attachments

None. Searches of WeilConjectures and Comparator in slopmaster2 by the item id, concept, and component/reduced keywords found no declaration stating the item.

## WANTED

WANTED: literature/stacks-project/varieties.tex, Varieties Lemma 09NE (varieties-lemma-glue-invertible-sheaves), for lem-sc-glue-component-reduced-cover-sections. The local source tree is absent; I read the Stacks Project web edition of Tag 09NE. Consequently proof_origin.by is agent, while every step retains its Stacks source place.

## Changes and limits

The imported statement is correct against 09NE's first paragraph and transition-function paragraph. The item had no proof; I supplied the finite clopen decomposition, the reduced affine ideal calculation, and the sheaf calculation. The blueprint ancestor place was already exact and same_as was already []; searches of the full imported blueprint for the reduced closed cover and section identity found no duplicate. No unresolved mathematical step remains.

## Review by C1

I read Stacks Varieties Lemma 09NE, proof from the definition of T through the displayed product identity. It says X is reduced, the closed Z_i cover X set theoretically, and the intersections are discrete for the parent gluing theorem. This item needs only reducedness and the set-theoretic finite closed cover: discreteness plays no part after T is removed. The statement also covers r=0 and r=1 consistently. I checked the three cited definition statements and the radical/zero-locus statement in their node files, as well as the earlier split of lem-sc-glue-component-line-bundles that uses this item.

Step 1 uses the closed-immersion statement's closed-image clause. Each W_i is closed in X minus T, the finite cover makes its complement closed, and membership in two W_i would put the point in T. The remaining work is finite-set topology. Step 2 uses the open-subscheme clause of def-pc-scheme, the affine quotient clause of def-weil-closed-immersion, the affine ideal identification in def-sbc-closed-immersion-ideal-sheaf, the explicit equivalence V(I)=V(J) iff their radicals agree in lem-weil-pbc-zero-locus-eq-iff-radical-eq, and the open-section-ring criterion of def-pc-reduced-scheme. These statements say exactly the facts invoked: on an affine V inside W_i, full support gives V(I)=V(0), hence sqrt(I)=sqrt(0)=0. Thus I=0 even if the original Z_i was nonreduced at T. Step 3 uses def-pc-scheme's locally ringed-space structure and its sheaf axiom; the only extra observation is that the intersections of distinct U_i are empty, so the compatibility conditions are vacuous. The sheaf restriction map is precisely the map in the statement.

I checked the hypotheses at their points of use: finiteness is needed for T to be closed and each W_i to be open; closed immersion gives affine quotient ideals; reducedness of X gives reduced rings on every affine V; no separation or Noetherian hypothesis is used. Small cases checked were X empty with r=0, a single component with T empty, two disjoint components, and X=Spec(k[x,y]/(xy)) with branches meeting at the origin. The same affine argument works if the x=0 branch is given the thickened ideal (x^2): the thickening vanishes away from the origin. The initial citation check rejected two excerpts as too short; I expanded them to the exact clauses of the definition statements, after which preflight passed. No mathematics changed. There are no new nodes to test or search in Mathlib. The existing Mathlib search record for this item has all three kinds; the grep and source-tree search found no exact Lean declaration.

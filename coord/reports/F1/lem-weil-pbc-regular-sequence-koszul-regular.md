# lem-weil-pbc-regular-sequence-koszul-regular

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-sequence-koszul-regular.json: split the existing statement, retaining its hypothesis and three conclusions. Four proof steps give the induction, the exterior-power/cone identification, an explicit positive-degree cycle chase, and the consequences for regular sequences. No new nodes.
- Mathlib verdict: no matching Koszul-regularity theorem. The item's recorded LeanSearch, LeanFinder, Loogle and grep searches remain valid; Mathlib/RingTheory/Regular/RegularSequence.lean lists Koszul regularity as TODO. The Mathlib mapping-cone construction is generic and does not assert this Koszul identification.

## Attachments

None. Read-only search of /home/ubuntu/weil-src-slopmaster2/WeilConjectures and Comparator for the node id, its blueprint tag, Koszul regularity, and regular/Koszul terminology found no declaration stating this item. Its existing lean_audit.slopmaster2.state is none; no attachment is justified.

## Wanted

None. Read Stacks more-algebra.tex from /tmp/stacks-project, corresponding to the listed literature/stacks-project/more-algebra.tex; tags 0628, 0629 and 062F were checked against tags/tags.

## Source and split

Stacks 062F has exactly the successive-injectivity hypothesis in the node and concludes vanishing of positive Koszul homology. Stacks 0629 identifies adjoining a sequence element with a cone, proved by exterior-power decomposition in 0628. I ran the induction from the final element, so 0629 applies in its stated order. The node proves the cone identity from its own Koszul differential and then chases cycles explicitly; it does not merely cite 0629 by tag. For degree one the cycle equation says multiplication by the final element kills the class in the prefix's degree-zero homology, so the stated injectivity is the precise hypothesis needed. For higher degrees prefix acyclicity handles the cycle. The empty sequence has no positive homology.

Whole-blueprint searches for 062F, regular Koszul, Koszul complex, regular sequence, and Koszul cone found no blueprint node stating this lemma; the few Koszul-complex results concern different constructions. No new node was created. The item's existing blueprint.from.place already identifies the exact role under thm-weil-pbc-finite-etale-lifting step 7, and same_as remains [].

## Checks

- python3 tools/review_split.py lem-weil-pbc-regular-sequence-koszul-regular: PASS, zero new nodes.
- python3 tools/check_dag.py --cycles: zero cycles and zero self-loops; exit 1 from seven reach and eleven route errors in other items, none introduced by this split.

## Wrong or unfinished

No statement or source error found. The source proof leaves the cone quasi-isomorphism as an invocation; this split writes the equivalent degreewise chase. Nothing remains to split in this item.

## Review by F1

I read Stacks More on Algebra 062F (`lemma-regular-koszul-regular`, `more-algebra.tex` lines 7265-7298) and its 0629/0628 cone references. The item's ring, module, ordered sequence, successive injectivity hypothesis, Koszul-regular conclusion and two regular-sequence consequences match 062F. The public `def-weil-pbc-koszul-complex`, `def-weil-pbc-koszul-regular-sequence`, and `def-weil-pbc-regular-sequence` statements were opened; they define exactly the differential, homology, and injectivity conditions used. No new node was made, and the whole-blueprint and slopmaster2 searches found no equivalent full statement (B1-B10).

Step 1 sets up induction and computes H0 of the prefix as the quotient by its earlier f_i, so the final injectivity applies there. Step 2 derives the exterior-power decomposition and the cone differential from the cited Koszul definition; I checked the sign in d(e_r wedge b)=f_r b-e_r wedge db. Step 3 treats n>1 by prefix acyclicity and n=1 by injectivity on H0, then explicitly subtracts D(0,-c) and fills the remaining cycle from H_n(A)=0. Step 4 invokes the public regular-sequence definition and specializes M=R. Each non-elementary input is a cited public definition; the cone identity is proved rather than assumed from an uncited source lemma (C1-C8, D1-D5).

I checked r=0, r=1, M=0, and n=1 in the cycle chase. No final-quotient nonzero condition is needed for the first assertion; it is only part of the stronger regular-sequence definition used for the consequences. The worker made no correction after handoff. `review_split.py` passes; `check_dag.py` finds no cycle, with unrelated baseline reach and route warnings from the contemporaneous audit refresh (E1-E7, A, F).

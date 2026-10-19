# Stage-1 report: lem-pur-first-quadrant-lowest-row-edge

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-first-quadrant-lowest-row-edge.json`: existing statement, split into five elementary steps; no exact Mathlib match.
- `citations.json`: a verbatim statement excerpt for every cited node in every proof step.
- `report.md`: this report. Search receipts remain in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is not the unit's key statement.

## Attachments

None. Searched the slopmaster2 project under `WeilConjectures/` for the exact item tag, first-quadrant spectral sequences, lowest-row language and edge maps. Read its `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean` and the edge portion of `Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean`. The former provides stable-page and abutment data, not this theorem; the latter defines edges for spectral objects and proves naturality, not the lowest-row criterion for a general spectral sequence with specified convergence data. Other hits are total-complex constructions, Grothendieck edges or scheme-specific cohomology edges. The read-only upstream master search likewise provides no proof attachment; upstream is reference material only.

## WANTED

None. All sources needed for this elementary proof are available locally.

## Findings and corrections

The item was unsplit and had no proof. Its statement is correct as written and is unchanged, including the recursive cycle/boundary definition of the stable term. Its four statement dependencies are retained. No hypothesis or conclusion is changed, and no STATEMENT-DISPUTED issue was found.

The source's Tag 0132 (`homology-lemma-first-quadrant-ss`) concerns convergence of double-complex spectral sequences; it is not a theorem giving this exact edge criterion. I read that statement and its proof, and do not invoke it. Here the finite filtration and convergence identifications are already hypotheses. The proof is marked agent-origin, extracted directly from Tag 011N (`homology-definition-spectral-sequence`), the recursive construction preceding Tag 011O (`homology-definition-limit-spectral-sequence`) and its bigraded variant, and Tag 0121 (`homology-definition-filtered`). No SGA source is used.

The current blueprint ancestor is `lem-pur-frame-independence`, reached through `lem-pur-relative-support-bottom-descent`. I read the first paragraph of the current main-20261015 frame-independence proof and the parent's statement. This item supplies the formal lowest-supported-degree edge argument needed for its sheaf-section passage. It neither asserts a support-sheaf purity calculation nor changes the frame-independence or unit route. The existing metadata still binds this created node to sk-prop-a1-kummer; no maintainer-owned binding is edited.

## Existing-node and Mathlib searches

Read the existing item searches and their listed results, retaining them. Ran the required Q03 searches through `msearch.py`, whose exact receipts are appended to `mathlib_searches`: LeanFinder with two different formulations, LeanSearch, Loogle, and grep. All services responded. The first grep's alternation query returned no hits; this alone was not used to claim absence. A second grep for `SpectralSequence` located Mathlib's actual definitions, and I read `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean` lines 15–44 and 124–143. I also read the two Loogle candidates in `Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean`, lines 276–285 and 371–380. They concern the isomorphism of intermediate maps of spectral-object windows when a complex-shape relation is absent. They do not identify a finite filtered abutment with its initial lowest-row entry. LeanSearch's short-complex zero-differential isomorphisms and LeanFinder's connected/single-complex homology results do not give the entire item in one specialization. Consequently this is a split, not a Mathlib leaf.

Whole-blueprint searches for spectral sequences and lowest-row language, DAG searches by the source tags and bidegree/edge language, and project-source searches found no exact existing statement to reuse. `lem-sp-edge-collapse` assumes every column other than column zero vanishes, a hypothesis absent here; a nonzero term in column one and row m is permitted by this item. `lem-sc-spectral-sequence-nat-row-zero` and `lem-weil-pbc-first-quadrant-row-collapse` assume all positive rows vanish and identify the opposite edge in arbitrary total degree. Neither can prove the present lowest-row claim. No new node is needed: propagation of zero through a subquotient, the explicit bidegree calculation, and finite descent are elementary arguments written in the item's steps, not separate lemmas.

## Review by Q03

I checked delivery-errors B through E against the actual item, all four cited definition statements, and the Stacks source. There are no new nodes whose statements or searches need a separate audit. The item introduces its category, pages, differentials, abutment, filtration and integer m. Its definitions are supplied by the four unchanged statement dependencies, and the meaning of the assumed convergence comparisons is written in its own statement. The proof never assumes an exact couple exists for this general spectral sequence: it uses precisely the recursive subobject construction expressly supplied in the item. The exact-couple-specific additional convergence notions in `def-sp-convergence` are not used.

Step 1 uses the successor-page-as-homology statement of `def-sp-spectral-sequence` and the zero object, kernels and cokernels available in `def-sp-abelian`. Its induction starts at page two with exactly the three stated vanishing regions. At each later page its cycles lie inside the zero middle object, and their quotient is zero. This includes all negative p and negative q, so later uses of the first-quadrant condition are justified, rather than merely presumed to persist.

Step 2 uses the initial conditions and inverse-image cycle/boundary recursion actually stated by `def-sp-convergence`. The incoming source has p=-r<0. The outgoing target has q=m-r+1<m: if nonnegative it is in a hypothesized vanishing row; if negative it is outside the quadrant. Thus both arrows are zero for every r>=2, even when m=0 or r>m+1. The recursively defined cycles stay equal to the whole original entry and boundaries stay zero, which proves canonical survival, not just an abstract isomorphism with some later page. The quotient by zero supplies the particular map s used by the edge.

Step 3 uses the same `def-sp-convergence` definition of E-infinity and the graded-piece definition in `def-sp-filtration`. The finite abutment identifications are a hypothesis of the item, not a theorem being attributed to either definition. Every index 1<=p<=m has 0<=m-p<m, so the corresponding initial entry and stable subquotient vanish. This proves exactly the zero graded pieces needed for descent, without imposing any vanishing in total degree above m.

Step 4 uses `def-sp-filtration` for the filtration inclusions and quotients, and the explicit normal-monomorphism axiom in `def-sp-abelian` for the only potentially hidden category-theoretic fact. I wrote out why a monomorphism with zero cokernel is an isomorphism: express it as a kernel of g, factor g through its zero cokernel to get g=0, and lift the identity through the kernel to construct an inverse. Monicity gives the other inverse equation. Thus this is a few-line consequence of cited definitions, not an uncited balanced-category theorem. Equal subobjects follow because this particular inclusion is an isomorphism over H. The finite downward induction starts at the given zero terminal step, and for m=0 the result is the terminal-step hypothesis itself.

Step 5 uses the quotient interpretation in `def-sp-filtration` and the stable cycle/boundary comparison of `def-sp-convergence`; the convergence isomorphism c is the one supplied by the item. It explicitly constructs the map H^m -> H^m/F^1 -> E-infinity^(0,m) -> E2^(0,m). Step 4 makes the first arrow a quotient by zero, whose inverse follows from its universal property. Step 2 makes the last arrow the canonical stationary comparison. This proves the actual edge map is invertible relative to the given convergence data, without an arbitrary choice of an isomorphism. No additional naturality theorem is silently asserted.

For B1–B10, the delivery has no new node, no proof in a statement, no Mathlib-leaf claim and no exact project attachment; all searches actually run have exact logged queries and receipts. The item and blueprint fields are preserved, `same_as=[]` follows the whole-blueprint search, and the split report names the ancestor passage. Source places use checked Stacks tags and labels, not changeable section numbering. TeX is represented normally in JSON.

For C1–C8, I opened every cited node and copied the relevant statement text into `citations.json`; none of the steps uses a cited node's proof or an unstated source lemma. All five steps are elementary definition expansions or explicit finite inductions with their bases and transitions supplied. Their union of uses is exactly `proof_deps`, there is no new dependency, and only definitions are taken from other units. There is no off-route theorem use to declare.

For D1–D5, the proof is carried by the item's steps, with no new restatement node, no circular use and no appeal to omitted standard arguments. The potentially hidden zero-cokernel argument and the exact edge composite are both written out. For the long-step rule, every step is below 2000 characters.

For E1–E7, checked small cases: m=0 gives no nonzero graded pieces to descend through and uses F^1H^0=0 directly; m=1 has outgoing q<0 on every page; m=2 has the r=2 target (2,1) in the vanished row and later targets outside the quadrant. A sequence concentrated at (0,m) gives the identity edge, and the all-zero sequence gives H^m=0 by the same finite filtration argument. An additional nonzero term at (1,m) is allowed, showing the proof never assumes the stronger all-column or all-positive-row collapse. The incoming and outgoing indices, all filtration ranges and the directions of the edge and convergence comparisons were checked. The argument needs neither infinite limits nor a smallness/complete-category hypothesis because the relevant cycle/boundary towers are constant or zero.

## Unfinished work

None for this stage-1 split. No Lean was written and no compiler, Lake or build command was run.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-artinian-etale-lift-smooth-point.json — statement, now split into five steps; no Mathlib match.
- citations.json — eleven step/node entries, each quote checked as a literal substring of the cited statement.
- searches.jsonl — the prescribed real searches for the item; earlier item searches retained in its JSON.

No new nodes and no new Mathlib leaves. The only DAG file delivered is the item.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for the Artinian/smooth lifting notion. The scheme declaration AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point in AlgebraicGeometry/SmoothArtinianLiftingAtPoint.lean:200 is not this algebraic-space assertion; it is the declaration already assigned to the scheme criterion node. No project declaration found supplies all clauses of this item.

## Literature

WANTED: none.

I read Stacks spaces-more-morphisms.tex Tags 061A (lemma-sheaf), 061C (lemma-action-sheaf), 061D (remark-special-case), 04AM (lemma-smooth-formally-smooth), and 0APN (lemma-lifting-along-artinian-at-point); etale-cohomology.tex Tag 03P2 (theorem-zariski-fpqc-quasi-coherent); sites-cohomology.tex Tag 03AJ (lemma-torsors-h1); more-morphisms.tex Tag 02HX (lemma-lifting-along-artinian-at-point); and spaces-descent.tex Tag 06F2 (lemma-smooth-smooth-local-source). These supply the torsor argument and the scheme-chart reduction used here. There is no SGA input.

## Corrections and scope

The imported item had a statement and no proof. Its reference to an etale-local Artinian variant needs an actual local-to-global argument: neither 0APN alone nor a definition of formal smoothness directly accepts those local lifts. Steps 1–2 now give the argument. The statement and every hypothesis are unchanged. This is not a statement dispute.

The item is a supporting node in the inherited Picard/moduli route to direct-image stability. I read its recorded chapter and unit, and the newest blueprint proof of direct-image stability (3) under literature/blueprint/latest. This auxiliary infinitesimal assertion is not itself a blueprint node. blueprint_refs.py ancestor returns None; I preserved that inherited null ancestor, its explicit place and full via list. Whole-blueprint searches for Artinian, lifting and smooth found no equivalent imported statement. I reused the existing pseudo-torsor, affine cohomology, torsor classification, smooth affine lifting, chart calculus, scheme Artinian criterion and smooth-source point locality. In particular the all-affine-tests scheme criterion lem-sfb-etale-local-infinitesimal-lifts-smooth cannot be applied directly to this pointwise Artinian hypothesis, and the flat-space smooth-locus lemma cannot be applied before flatness is known.

The declared generic off-unit tools are lem-sc-etale-affine-qcoherent, lem-sc-torsor-h1 and lem-weil-pbc-smooth-artinian-lifting-at-point. They implement the literature's local argument and do not replace a unit-level route.

## Mathlib search review

I ran leanfinder twice with different phrasings, loogle, grep through the prescribed command, and leansearch, with their exact texts copied from searches.jsonl. All services answered. Loogle and grep returned no hits; semantic searches returned scheme smoothness, ring smooth loci and formally smooth algebras. I read Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean, Mathlib/RingTheory/Smooth/Locus.lean and Mathlib/RingTheory/Smooth/Basic.lean to check the plausible hits. These concern schemes or rings and require other hypotheses than the pointwise Artinian etale-local property here; they are not a one-line specialization giving this algebraic-space statement. The live source uses Smooth with the deprecated IsSmooth alias, while some semantic hits use the older name; the difference does not yield an attachment.

## Not duplicates

No new nodes were created. Existing statements with 04AM and 0APN references were inspected and reused when they give an ingredient; no existing statement was copied into a fresh node.

## Review by Q52

I checked the complete B–E checklist with the statements and the Stacks sources open. There are no unsplit new statements, data definitions or hidden replacement clauses. Every proof dependency is the statement of an existing node, and proof_deps is exactly the union of step uses. All steps have sources and an explicit elementary judgement; none exceeds 2000 characters. I checked that none of the cited statements depends transitively on this item.

Step 1 uses def-sbc-first-order-thickening for the quotient affine thickening and lem-sfb-space-infinitesimal-lift-pseudotorsor for the sheaf of compatible maps, its quasi-coherent coefficient module and its simply transitive action. I read that entire statement: it does not assert nonemptiness. Nonemptiness comes precisely from the item's covering hypothesis. The local section identifies the restricted sheaf with the coefficient group by translation, so def-sc-gm-torsor, whose final clause explicitly allows every abelian sheaf, gives a torsor. Local finite presentation of f and square-zero of the ideal are exactly the hypotheses of the pseudo-torsor node; no smoothness of f is being assumed.

Step 2 uses lem-sc-etale-affine-qcoherent with the affine scheme Spec B' and the quasi-coherent H supplied in step 1. It gives vanishing in degree one on that very scheme's small etale site. I checked that lem-sc-torsor-h1 concerns arbitrary abelian sheaves on an arbitrary scheme, not only G_m or curves, and explicitly sends zero to the trivial torsor. An isomorphism from the trivial torsor carries its zero section to a global lift, with both equations built into the sheaf's definition. Thus the local maps are not incorrectly assumed to agree on overlaps.

Step 3 uses the surjective scheme atlas in def-trf-algebraic-space to choose u over x. The statement of def-sfb-space-morphism-properties tests local finite presentation on every compatible pair of etale scheme charts; the identity S to S is such a target chart, so g=fq is locally of finite presentation. I read lem-sfb-stack-chartwise-smooth-etale-calculus: it explicitly gives both etale implies smooth and local finite presentation implies local finite type, for representable maps as used here. The argument imposes no quasi-compactness or separation condition on the atlas.

Step 4 uses lem-sfb-smooth-space-affine-infinitesimal-lift only for q, which is already smooth by step 3, not for f. Its source is the scheme U, its target is X, its base scheme is S, and both test schemes are affine. The bottom map is the actual global gamma from step 2, and q b = gamma j. Its two stated lifting equations imply delta j=b and g delta=c by the displayed composition calculation. Every Artinian test centered at u is sent to one centered at x, as required by the hypothesis. I did not assume Artinian etale covers have sections.

Step 5 uses exactly the equivalence (1)–(2) in lem-weil-pbc-smooth-artinian-lifting-at-point. The criterion itself states that its small extensions have square-zero kernel, so step 4 covers them. S is locally Noetherian as required, and g is locally of finite type by step 3; no finite-type condition on residue fields is added. The statement of lem-sfb-space-smooth-source-point-locality explicitly gives pointwise descent along a smooth map without requiring surjectivity, and defines its conclusion by the existence of an open neighbourhood. It supplies the exact final open-subspace conclusion; no fibre criterion with a missing flatness hypothesis is used.

For edge cases I checked zero kernel (the lift is already a map on the same affine scheme), arbitrary residue fields, nonseparated spaces and empty X (there is then no x). The criterion still detects a nonreduced nonsmooth example: for X=Spec k[e]/(e^2) over k at its sole point, take B=k[t]/(t^2), B'=k[t]/(t^3), e mapping to t. A lift would send e to t+a t^2, whose square is t^2, nonzero. A jointly surjective etale cover cannot kill this obstruction, by faithful flatness; thus the hypothesis fails as expected in every characteristic. No new statement needed an additional small-case repair. The corrections were to the missing proof, not to the imported assertion.

## Unfinished work

None in this stage-1 split. The existing supporting nodes remain under their existing project statuses; their statements, rather than any unrecorded proofs or constructions inside them, are what the five steps use. Required server dry run and direct delivery are run after this report is written.

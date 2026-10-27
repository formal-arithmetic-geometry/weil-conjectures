## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-artin-nonversal-thickening-tower.json (statement, split; not in Mathlib), citations.json, report.md. No new nodes and no new Mathlib leaves.

Attachments: none for the item. The live source search by blueprint tag, nonversal/non-versal, Schlessinger and thickening-tower concepts found no project declaration stating it. The existing closed ideal-filtration theorem was inspected while considering a lower-level route, then not used because the existing single-point obstruction is the correct input.

WANTED: none.

The statement and statement dependencies are unchanged. Stacks artin.tex Tag 0G2S (lemma-infinite-sequence-pre), read in full, supplies the route. Tag 0G2J (lemma-single-point), read with its proof, supplies a single-point obstruction. A same-day shared-DAG update supplied lem-sfb-artin-single-point-obstruction during this session; it was opened in full and reused. Searches of the whole DAG and blueprint by 0G2S, 0G2J, single-point, nonversal, non-retractable, small extension and residue-field-kernel phrases found no other exact blueprint node. The current literature/blueprint/latest direct-images proof and unit were read. Their broad direct-image route is retained through the inherited supporting Artin-openness input; blueprint_refs.py ancestor returns null, which is retained in the item. No chapter or unit fields are edited.

The source's last sentence omits details of a local identification of U_n and T_n after removing earlier support points. For this item's exact conclusion these details are unnecessary: restriction of a proposed retraction along the coordinate map T_n to U_n already contradicts the single-point obstruction. The proof gives that argument explicitly, with its reduction isomorphism. We do not claim the omitted residue-field transition-kernel clause (2) of 0G2S as part of the item, although the construction also has that property. No source error or statement dispute was found.

Exploratory Mathlib searches were run exclusively through msearch.py and their actual hits are retained in searches.jsonl. The semantic searches for nonversality and small extensions returned formal smoothness of rings, Artinian spectra and general quotient facts, not this assertion about fibred groupoids. Loogle found formal-smooth ring results for Algebra.FormallySmooth, RingHom.ker and no hits for IsArtinianRing, CompositionSeries or IsArtinianRing, RingHom.ker. The grep queries found no relevant deformation assertion. No new node records are introduced, so there is no unlogged new-node search claim. Existing inherited item search records are preserved verbatim.

Nothing remains unfinished in the split. Existing statement-only dependencies remain separate queue items, as required in stage 1.

## Not duplicates

No new nodes. The single-point obstruction, ideal-filtration and ring-fibre-product candidates were found in the live DAG before creating anything. Only lem-sfb-artin-single-point-obstruction is needed in the delivered proof; it concerns one obstruction over an arbitrary affine Noetherian base, whereas this item assembles countably many obstructions over Spec Z into a compatible tower.

## Review by Q10

I read Stacks artin.tex 0G2S and its 0G2J input in full, as well as more-morphisms.tex lemma-pushout-along-thickening and more-algebra.tex 01Z8 (lemma-diagram-localize) when considering the source's locality argument. I also read the latest blueprint unit and direct-image proof, the chapter/unit records, GOAL.md, the human's three-level restrictions and delivery-errors B--E. There are no new nodes requiring a further source review.

Step 1 uses the statement of lem-sfb-artin-single-point-obstruction, not its proof. It states the affine ring extension, square-zero residue-field kernel, prescribed reduction isomorphism and precisely the local arrow prohibition required here. Its Noetherian base hypothesis holds for Z (all ideals principal), and its finite-type, fibred-groupoid, gluing and nonversality hypotheses are all hypotheses of the item. The item has no representable-diagonal or limit-preservation assumption; neither is required by the cited single-point statement. All objects needed to apply it are introduced.

Step 2 cites def-weil-affine-spectrum for the contravariant scheme maps, def-weil-closed-immersion for the surjective affine-ring criterion, and def-sbc-first-order-thickening for the square-zero criterion and underlying-space identification. I reopened these three statements and verified each quoted clause. Surjectivity is proved by lifting the common coordinate; the composite kernel is literally the finite product of the I_i, and its square is zero coordinatewise. No flatness, localization exactness or general scheme-pushout theorem is hidden in this step.

Step 3 uses exactly the gluing equivalence spelled out in the item's hypotheses, with A=R_{n-1}, B=R_0, B'=S_n. Its surjection and square-zero hypotheses were established in steps 1--2. The specified isomorphism is retained as part of the fibre-product groupoid object, so the transition and final reductions have the needed compatibility. This is an elementary application of a stated hypothesis, with no external lemma or stack descent.

Step 4 again cites the full single-point prohibition. The coordinate map T_n to U_n is over the common reduction U; its inverse image of a neighbourhood contains u_n. Pullback composes the base retraction with this coordinate map, and the chosen fibre isomorphism from step 3 identifies the restricted object with y_n while preserving the reduction. Thus the identity on U is precisely the identity prohibited by the cited statement, not an unspecified isomorphism. All five step/dependency pairs have verbatim statement quotations in citations.json.

Edge cases checked: n=1 gives the original single-point extension; at n=0 the ring and object are unchanged; zero composite kernels still define first-order thickenings, but cannot furnish a nonversal single-point obstruction; an empty U or a U with too few incomparable nonversal points has no sequence satisfying the hypotheses. No finite-type assertion is imposed on the S_n or R_n, and none is used. The proof uses no separation or stack hypotheses. Each step is under 2000 characters, and the elementary steps contain only explicit ring calculations, an assumed equivalence, or composition and pullback of the specified arrows. No clauses are merely renamed into new nodes. No source on the prohibited SGA route is used.

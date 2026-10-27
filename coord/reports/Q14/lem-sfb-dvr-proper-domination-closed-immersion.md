# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-proper-domination-closed-immersion.json`: statement, split; unchanged statement and statement dependencies, six proof steps, no Mathlib match for the whole assertion.
- `citations.json`: nine citations, with the full verbatim statement of each cited node.
- `searches.jsonl`: searches actually run by msearch.py, retained unchanged.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves and Lean-closed valuative tools are reused.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's exact blueprint tag, proper-domination terminology, and DVR/immersion combinations. There is no project declaration stating the item exactly. Existing project Noetherian DVR properness statements are not attachments for this assertion.

## WANTED

None. The required sources are present locally.

## Findings and changes

The imported node was statement-only. Its statement is correct as written; no dispute or correction was necessary. The proof follows Stacks `limits.tex`, Tag 0208, `lemma-Noetherian-dvr-valuative-proper`, the diagram `equation-solid` and the concluding contradiction. The source uses projective space and birational Chow domination to test only generic function fields. Here the item's hypothesis tests every DVR square, so birationality and surjectivity of pi are unnecessary, and separatedness of the ambient map q supplies exactly the uniqueness used in that argument. Properness of q is unnecessary.

Before creating any node I searched the whole DAG for the valuative tags and relevant keywords and ran blueprint_refs searches for DVR, closed image, proper domination, and DVR lifts. The exact tools already exist. In particular, `lem-sfb-noetherian-image-boundary-dvr` supplies both the DVR square and its closed-point value; I did not replace it with a weaker statement about ordinary specializations. I used the existing immersion/lft, locally-Noetherian/qs and qcqs-permanence nodes for finite type, rather than introducing an elementary assembly lemma. The blueprint ancestor command prints no id for this inherited chain; the item's existing null from.node and via chain are retained, and same_as is empty. This is below the fixed chapter/unit route and implements the existing properness prerequisite of constructibility stability.

The five recorded 2026-10-22 searches in the item were retained. I ran new leanfinder searches with two phrasings, leansearch, loogle and Mathlib grep through msearch.py. All services answered. Returned results included IsClosedImmersion.of_isPreimmersion / iff_isPreimmersion, IsClosedImmersion.of_comp, immersion local finite type, and the ordinary valuative criterion. I read ClosedImmersion.lean:61-67, Immersion.lean:190-192 and ValuativeCriterion.lean:230-240,274 onward. The closed-image criterion assumes the closedness we must prove; of_comp assumes the composite is a closed immersion; the general valuative criterion quantifies over all valuation rings. None is the whole item or a one-line specialization giving it. The new records use exactly the query strings from searches.jsonl, with actual result metadata and no invented searches.

## Review by Q14

I read the source proof in `limits.tex` Tag 0208 in full through its final contradiction and the boundary-trait construction in Tag 0CM2 (`lemma-reach-point-closure-Noetherian`). I also read the statements and arguments for `morphisms.tex` Tag 01T5, `properties.tex` Tag 01OY, `schemes.tex` Tag 01IQ, the valuative existence criterion Tag 01KF, and separated uniqueness Tag 01KZ. The three blueprint levels in SETUP.md, the unit and chapter records, and delivery-errors B through E were checked against this proof. There are no new statements requiring a source audit or duplicate comparison.

Step 1 uses exactly the statements of `lem-weil-pbc-locally-noetherian-quasi-separated`, `lem-weil-pbc-qcqs-morphism-permanence` clause (1), `lem-weil-pbc-immersion-base-change-lft` clause (2), and `def-weil-finite-type-morphism`. I opened each node. P is locally Noetherian by the item's explicit meaning of Noetherian, so it is quasi-separated; Y is explicitly quasi-compact. These are the precise source/target hypotheses of the permanence assertion. Local finite type and quasi-compactness then mean finite type by definition. This avoids assuming quasi-compactness of i without proof.

Step 2 cites `lem-sfb-noetherian-image-boundary-dvr`, whose statement gives a DVR A, its fraction field K, u and v with iu=vj and v(s_A)=p. Both of its hypotheses, finite type and locally Noetherian target, were established in step 1. We choose p outside the image, so this is the safe boundary-only statement, not the unrestricted fixed-generic-field claim in 0CM2. No generic-point or residue-field identification is used.

Step 3 is elementary: write a=pi u, b=qv, and fa=f pi u=q i u=q v j=bj. The hypothesis of this item itself supplies h with fh=b and hj=pi u. The generic map in the next square is u, not merely a point of Y, and no uniqueness of this h is assumed.

Step 4 uses the explicit equivalent valuation-ring characterization in `def-sc-discrete-valuation-ring` and the statement of `lemma-nagata-proper-valuative-criterion-existence-api`. I read its original statement and its main-20261015 blueprint_update: the latter gives existence for universally closed morphisms, so in particular for the given proper pi. The square commutes because pi u=hj; the conclusion gives BOTH pi w=h and wj=u. Thus q i w=f pi w=fh=qv, as needed for step 5. There is no base-Noetherian or excellence requirement here.

Step 5 uses `lemma-nagata-separated-valuation-lift-unique` literally for q:P to S. The two maps iw and v have the same composite b to S and the same restriction to Spec K, using wj=u and iu=vj. Its sole geometric hypothesis, separatedness of q, is an explicit assumption. Equality at the closed point contradicts p outside i(Y). This step uses neither separatedness of f nor surjectivity of pi.

Step 6 uses the full statement of `lem-weil-pbc-immersion-closed-image-closed-immersion`, the existing Mathlib leaf for 01IQ. The contradiction proves closedness of the entire image, and immersion was assumed, exactly matching that criterion. No sheaf-theoretic closed-subscheme construction is hidden here.

For C4 I copied the statements of all nine uses into citations.json after opening them; each quoted assertion supplies the named step. For C1 every non-elementary fact above has a node. The only node-free step is the displayed compositional identity and an application of the item's own assumption. No step hides a separate comparison lemma, and every step is below 2000 characters. The union of uses is proof_deps. Existing tool nodes are Mathlib leaves/Lean-closed or in the same unit; no off-route replacement is needed. No SGA source is cited.

Small cases: Y empty makes the image empty and the boundary case impossible. For a closed immersion the boundary is empty, as expected. For G_m into A^1 with pi the identity and f:G_m to Spec k, the extension condition fails for A=k[t]_(t), K=k(t), and generic coordinate t, so this familiar nonclosed immersion is not a counterexample. Even when f is nonseparated, the argument only needs existence for f and uses uniqueness for q. Disconnected Y is handled by the existing image-boundary lemma without choosing an irreducible component. These checks found no missing hypothesis.

## Validation

Server review_split passed before packaging, reporting zero new nodes. The full deliver.py dry run and push are recorded by the delivery command output; no local DAG checker, Lean compiler, Lake, git command, or repository write was used.

## Unfinished work

None at stage 1. Existing child nodes retain their own queued proof obligations; this delivery does not claim to finish those proofs.

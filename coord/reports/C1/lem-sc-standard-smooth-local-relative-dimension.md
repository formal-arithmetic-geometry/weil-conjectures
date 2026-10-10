1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-standard-smooth-local-relative-dimension.json`: item, statement split; no new nodes.
   - `citations.json`: verbatim statement excerpts for each cited node and proof step.
   - This report.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. I retained its statement and filled the missing standard-smooth definition dependency. The proof uses the already reviewed nodes for local standard smoothness and for the rank of relative differentials, then compares that rank with the n-c rank supplied by the standard-smooth Kähler basis.

## Review by C1

I read the item source in `literature/stacks-project/morphisms.tex` (Tags 02G2 and 054L), the local standard-smooth source (Tag 01V7), the differential-rank source (Tag 02G1), and Algebra Definition 00T6 and Lemma 00T7(2). The statement's hypotheses match the smooth pure-relative-dimension setup, and the added `def-weil-pbc-standard-smooth-algebra` dependency supplies the meaning of “standard smooth” and its relative dimension.

Step 1 cites the existing differential-rank node, whose statement explicitly gives affine neighborhoods and a free differential module of rank d. Step 2 cites the existing local-standard-smooth node, whose statement gives affine neighborhoods over which the ring map is standard smooth; restriction to open subschemes and taking an affine common refinement are the local elementary operations used here. Step 3 cites the standard-smooth Kähler-basis node for rank n-c and the definition node for the meaning of relative dimension n-c, and reuses the rank-d conclusion from step 1. The rank comparison after localization is the elementary localization invariance of a finite free module.

I searched the full DAG and blueprint before adding dependencies; no new node was needed. Mathlib searches for the item were run with `msearch.py` using LeanFinder, Loogle, grep, and a second LeanFinder phrasing; Mathlib's chart class was recorded as a non-match because it assumes Mathlib's chart-defined notion rather than the project's fibre-dimension hypothesis. Small cases d=0 and a polynomial affine-space chart reduce to c=n and c=0 respectively, agreeing with the stated relative dimension.

## Second reading by C1

- Item statement: checked against Stacks Tags 02G2 and 054L; the smoothness, pure relative dimension, point, and affine chart hypotheses agree.
- Step 1: checked against `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`; its statement supplies the affine neighborhoods and free differential module of rank d used here.
- Step 2: checked against `lem-weil-pbc-smooth-locally-standard-smooth`; applying it to the Step 1 restriction gives a chart inside that affine neighborhood, and the revised text spells out the localization preserving the free rank.
- Step 3: checked against `lem-weil-pbc-standard-smooth-kahler-basis` and `def-weil-pbc-standard-smooth-algebra`; they state the rank n-c and define n-c as relative dimension. The step is non-elementary because it compares the two rank conclusions.
- New nodes: none; all dependencies pre-existed. The full DAG duplicate and blueprint searches were checked in the worker record.
- Edge cases: d=0 gives n=c, and affine d-space gives c=0 and n=d; both satisfy the claimed relative dimension.
- Changes: repaired Step 2's vague intersection language, marked Step 3 non-elementary, and added this independent second-reading record. No statement or source tag changed.

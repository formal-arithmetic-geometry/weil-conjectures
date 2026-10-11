## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-ML-ordinals.json`: existing item, split into five proof steps; no new nodes.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `lem-pur-kinjective-ML-ordinals`, `0AAT`, or `ML-over-ordinals`.

## WANTED

None. The source file needed for the proof is available at `/home/ubuntu/c1-stacks-review/homology.tex`.

## What I checked

I read Stacks Project Homology, Lemma Tag 0AAT (`lemma-ML-over-ordinals`), including its transfinite-induction proof at lines 7861--7915. The imported item statement agrees with the lemma: an ordinal-indexed inverse system of acyclic complexes with each map from a stage to the preceding limit termwise surjective has acyclic inverse limit. I also read the surrounding use in `dag/nodes/sec-smooth-purity/lem-pur-kinjective-characterize-K-injective.json`; its limit-stage application supplies exactly this statement and does not require a stronger conclusion.

The five steps follow the source in order. Step 1 records the strengthened transfinite induction hypothesis, which is needed at limit ordinals. Step 2 handles degree zero at the initial stage using acyclicity. Step 3 gives the explicit successor correction: the compatibility defect is a boundary and is lifted through the assumed degreewise surjection. Step 4 repeats that correction at a limit stage after invoking the induction hypothesis for the earlier limit complex and the termwise-surjective map from the current stage. Step 5 applies the same argument after shifting to all degrees. No step cites a proof rather than a statement, and no non-elementary auxiliary fact was hidden in the split.

I searched the whole DAG for the Stacks tag, the lemma label, and ordinal inverse-limit acyclicity; the only related node is the current consumer `lem-pur-kinjective-homotopy-limit-vanishing`, which cites this item and is not a duplicate. I searched the blueprint with `tools/blueprint_refs.py`; no blueprint node states this lemma. The project Lean source contains no matching declaration. Mathlib searches were run with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch; LeanFinder and Loogle returned only unrelated general limit or homological-complex declarations, grep found no match, and LeanSearch was unavailable (recorded as such in the node). I tested the base and successor clauses against the source's explicit equations, including the sign-free degree-zero case and the correction by `d(z_beta)`.

## Review by M1

I checked the item against Stacks Tag 0AAT and verified every hypothesis: the index is an arbitrary ordinal, each stage is acyclic, and the map to the inverse limit over every earlier segment is surjective in every degree. The successor step uses only the displayed surjectivity in degree `-2` and acyclicity in degrees `0` and `-1`; the limit step uses the strengthened induction hypothesis exactly as the source does. The final shift argument supplies exactness in every degree. Existing downstream citations use the conclusion only to deduce acyclicity of the inverse-limit Hom complex. No new node was created, so there are no duplicate or auxiliary-node issues to review.

## Second reading by M1

- Item statement: checked against Homology Tag 0AAT (`lemma-ML-over-ordinals`), lines 7861--7872; ordinal indexing, acyclicity, predecessor-limit surjectivity, and acyclic inverse limit agree hypothesis by hypothesis.
- Step 1: checked against the transfinite-induction paragraph at Tag 0AAT, lines 7884--7887; the simultaneous induction formulation is elementary and supplies the limit-stage hypothesis.
- Step 2: checked against the beta=0 construction at lines 7890--7892; the degree-zero cocycle and acyclicity implication are correct.
- Step 3: checked against the successor correction at lines 7894--7905; the defect, boundary lift, and correction signs are stated explicitly and use the given degreewise surjectivity.
- Step 4: checked against the limit-stage paragraph at lines 7907--7913; expanded the omitted “same argument” into the preimage, defect, boundary, lift, and compatibility equations.
- Step 5: checked against the conclusion after the displayed proof at lines 7914--7915; expanded the shift argument to identify degree-n cocycles and boundaries and preserve surjectivity.
- New nodes: none; there were no new statements to audit for B1--B7, duplication, or Mathlib status.
- Changes: repaired steps 4 and 5 to remove “same argument” omissions under E5 and make the limit correction and all-degree shift self-contained; no statement or citation changed.

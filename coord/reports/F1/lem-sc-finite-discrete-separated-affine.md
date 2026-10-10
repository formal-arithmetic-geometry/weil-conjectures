1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-finite-discrete-separated-affine.json`: item split; one proof step.
   - `citations.json`: one verbatim citation for step 1.
   - No new nodes; the existing `lem-weil-pbc-finite-discrete-scheme-affine` is used.

2. Attachments:
   - No Lean declaration attachment. The source search found no declaration tagged `lem-sc-finite-discrete-separated-affine` and no sorry-free declaration stating this exact item.

3. WANTED:
   - None.

4. What was checked and changed:
   - I read the item node, its parent blueprint ancestry, the `sk-thm-curveestimate` unit, and the Stacks source location Properties Lemma 0CKV. The item statement and hypotheses are retained exactly.
   - Before creating anything, I searched the whole DAG and blueprint. The existing node `lem-weil-pbc-finite-discrete-scheme-affine` states the stronger fact that any scheme with finite discrete underlying space is affine, and its statement directly supplies the only non-elementary fact used by step 1. Its Mathlib leaf and source searches were read; it records `AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCommRingCat` in `Mathlib/AlgebraicGeometry/Limits.lean:700`.
   - Step 1 checks that the item's finite-discrete hypothesis matches the existing node's hypothesis; quasi-compactness and separatedness are additional assumptions and are unused. The conclusion is exactly the existing node's affine conclusion. The step source is the final assertion of Properties Lemma 0CKV.
   - I tested the statement on the empty scheme, a one-point affine scheme, and a finite disjoint union of affine one-point schemes; all satisfy the stated conclusion. No new node or un-cited fact was needed.

## Review by F1

I checked the split against delivery-errors B-E. The only proof step cites `lem-weil-pbc-finite-discrete-scheme-affine`, and the verbatim quote in `citations.json` is copied from that node's statement. The step uses only the finite-discrete-to-affine assertion; the item's quasi-compact and separated hypotheses are present but not needed. The existing node was found by a whole-DAG keyword search and is a Mathlib leaf with the finite/discrete `IsAffine` instance recorded and source-checked. The item keeps its Stacks 0CKV source, has its blueprint `from.place` filled, and has no new unsplit nodes or hidden tag-only facts.

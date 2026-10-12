## What changed

Added a decomposition lemma for the overlap of a quasi-compact open and an affine open,
and used Mathlib's finite affine cover induction to prove the main theorem from it.

## Proved and sorry left

`AlgebraicGeometry.quasiCompactOpen_induction` is proved. The new theorem
`AlgebraicGeometry.property_intersection_of_quasiCompact_affine` remains `sorry`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The direct DAG proof requires substantial separatedness and affine-intersection glue;
this delivery isolates that step as a strictly simpler intermediate theorem.

## Earlier second reading (a previous round; superseded)

The proof compiles and preserves the target statement; the new intermediate statement is strictly simpler.

## New nodes

`property-intersection-qc-affine` in `dag/nodes/sec-curve-estimates/property-intersection-qc-affine.json`.

## Second reading by K3

1. I compared the delivered module with the repository version. The existing theorem signature is byte-for-byte unchanged; only its proof and the explicitly new intermediate module differ. Verdict: pass.

2. I compiled all three sandbox modules with the prescribed launcher. They compile without errors or warnings after removing a duplicate import and shortening a docstring line. The main theorem has no `sorry`; the split intersection theorem is the only remaining named hole and is documented with its source and proof plan. Verdict: pass.

3. The split theorem is a strict reduction: it isolates the overlap case needed by the finite affine induction and does not restate the target. Its hypotheses and conclusion match the overlap assertion in the Stacks proof. Verdict: pass.

4. The proof follows Mathlib's `compact_open_induction_on`, uses the affine base case and the gluing hypothesis, and calls the split overlap theorem. The separated-open import remains needed by that theorem; the duplicate intersection import was removed. Verdict: pass.

5. The DAG proof and `proof_deps` now match the Lean route, with the new overlap node as the sole non-Mathlib dependency. The unit realization remains attached to the target node. Verdict: pass.

Changed the duplicate import, fixed the long documentation line, and updated the target node's proof route and dependencies to reflect the actual proof.

## Second reading by K3

1. I compared the delivered module with the repository version. The existing theorem signature is byte-for-byte unchanged; only its proof and the explicitly new intermediate module differ. Verdict: pass.

2. I compiled all three sandbox modules with the prescribed launcher. They compile without errors or warnings after removing a duplicate import and shortening a docstring line. The main theorem has no `sorry`; the split intersection theorem is the only remaining named hole and is documented with its source and proof plan. Verdict: pass.

3. The split theorem is a strict reduction: it isolates the overlap case needed by the finite affine induction and does not restate the target. Its hypotheses and conclusion match the overlap assertion in the Stacks proof. Verdict: pass.

4. The proof follows Mathlib's `compact_open_induction_on`, uses the affine base case and the gluing hypothesis, and calls the split overlap theorem. The separated-open import remains needed by that theorem; the duplicate intersection import was removed. Verdict: pass.

5. The DAG proof and `proof_deps` now match the Lean route, with the new overlap node as the sole non-Mathlib dependency. The unit realization remains attached to the target node. Verdict: pass.

Changed the duplicate import, fixed the long documentation line, and updated the target node's proof route and dependencies to reflect the actual proof.

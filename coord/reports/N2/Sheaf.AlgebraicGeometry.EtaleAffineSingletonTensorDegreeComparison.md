## What changed

Added the degreewise decomposition theorem
`exists_singletonTensorDegreeComparison_degree`, whose proof is left as a named
stage-3 node. The original theorem now assembles the degreewise choices with
`choose` and is fully proved. The parent node's proof dependencies were reduced
to the new degreewise node.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison` by
choice and dependent assembly. One new sorry remains in
`exists_singletonTensorDegreeComparison_degree`, node
`new-etale-affine-singleton-tensor-degree-comparison-degree`; it is the fixed
degree affine tensor-section calculation.

## No longer needed

The parent theorem's direct imports and proof dependencies are no longer used by
its Lean proof; they remain public imports because the definitions and statement
need them. The direct geometric proof steps are represented by the new
fixed-degree node.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the independent affine calculation for every degree
with the logical assembly of the family. No mathematical statement was wrong;
the proof was decomposed into a strictly fixed-degree geometric statement and a
real choice argument.

## New nodes

`new-etale-affine-singleton-tensor-degree-comparison-degree` records the fixed
natural-number degree calculation and its source and proof plan.

## Earlier second reading (a previous round; superseded)

The decomposition theorem has a strictly fixed degree and the parent proof is a
real dependent-choice assembly; signatures are unchanged and the unit route is
preserved. The fixed-degree statement is exactly the corresponding component of
the affine calculation.

## Second reading by N2

1. Compared the delivered module with the repository version. Existing declaration signatures and definitions are unchanged; only the parent proof and a new fixed-degree declaration were added. Verdict: pass.

2. Compiled all sandbox modules with `lcompile.py --all`. There are no errors or forbidden declarations. The parent theorem is proved; the only remaining `sorry` is the named fixed-degree theorem. Verdict: pass.

3. Checked the fixed-degree statement against the affine tensor calculation and searched the library and Mathlib search logs for duplicates. It is a genuine strict decomposition, with source, proof plan, and node recorded. Verdict: pass.

4. The parent proof takes the shortest route: apply the fixed-degree theorem for each natural number and assemble witnesses with `choose`; the affine unit route is retained in the split node. Verdict: pass.

5. Updated the parent node's proof and `proof_deps` to match the Lean proof, while leaving the unit and fixed-degree node route intact. Verdict: pass.

Changed in this reading: corrected the parent DAG proof metadata and added this review record. No Lean source changes were needed.

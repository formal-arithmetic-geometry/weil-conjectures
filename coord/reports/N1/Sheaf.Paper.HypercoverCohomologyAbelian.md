## What changed

Replaced the proof of `AlgebraicGeometry.hypercover_cohomology_abelian_part` with the first
projection of the existing source-library theorem
`AlgebraicGeometry.hypercover_cohomology`. Added a proof-only import of
`WeilConjectures.AlgebraicGeometry.HypercoverCohomology`.

## Proved and sorry left

The declaration `AlgebraicGeometry.hypercover_cohomology_abelian_part` is proved. No new
`sorry` declarations were added.

## No longer needed

The injective-resolution, refinement, free-resolution, K-injective, spectral-sequence,
and sheaf-colimit imports and DAG dependencies listed in the original plan are unused by
the proof and are pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan duplicated a theorem already present in the source library. The source
library theorem has exactly the required abelian conclusion as its first conjunction
component, so the long planned argument is unnecessary for this item.

## New nodes

None.

## Second reading by N1

1. Compared the delivered Lean module with the repository version. The theorem signature and
   docstring are byte-for-byte unchanged; only the proof and proof-only import changed.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. There are no
   remaining `sorry`s in the delivered module, and the proof uses the existing source-library
   theorem without introducing axioms or definitions.
3. Checked the reduction against the existing declaration and searched Lean/Mathlib for an
   independent hypercover-cohomology result. The first conjunction component has exactly the
   target type, so the projection is true and exactly as strong as required; no new statement
   was introduced.
4. Confirmed that the proof takes the shortest available route. The former injective-resolution,
   refinement, free-resolution, K-injective, spectral-sequence, and colimit-support imports are
   unused and were removed as proof-only dependencies. The source theorem remains the unit's
   realized route, so no unit step is bypassed.
5. Updated the DAG node's `proof`, `proof_deps`, and `proof_origin` to match the Lean proof.
   The node has no new split-off holes, and the report records the pruned dependencies.

Changed: replaced the long `sorry` proof with the first projection of
`AlgebraicGeometry.hypercover_cohomology`, changed the proof-only import accordingly, and
updated the node metadata and report.

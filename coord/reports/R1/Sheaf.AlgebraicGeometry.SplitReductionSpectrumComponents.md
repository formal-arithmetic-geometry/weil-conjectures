## What changed

Added a complete composition proof of `spectrum_components_of_split_reduction`.
The argument is factored through `exists_split_reduction_open_partition` and
`isUniversalHomeomorphism_split_reduction_component`, which are documented
intermediate statements and currently remain the only proof holes.

## Proved and sorry left

Proved `spectrum_components_of_split_reduction` by applying the factor-thickening
intermediate result and the local `universalHomeomorphism_of_thickening` helper.
The new declaration `exists_split_reduction_factor_thickenings` contains the
remaining `sorry`.

## No longer needed

No imports were removed. The existing proof dependencies remain necessary for
the two intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The original module had one monolithic hole, while the stated DAG proof has two
independent conceptual steps. No mathematical statement was changed.

## New nodes

Added `lem-weil-pbc-split-reduction-factor-thickenings`, matching
`exists_split_reduction_factor_thickenings`.

## Earlier second reading (a previous round; superseded)

Pending independent reading: verify that the composition proof preserves the
original target statement and that both intermediate statements are strict
substeps of the DAG proof.

## Second reading by R1

1. I compared the delivered module with the repository version. The target declaration signature and all existing declarations are unchanged; the only implementation change is the proof and its proof-only import of the new factor-thickening module.

2. Both sandbox modules compile cleanly with `lcompile.py`. There are no axioms, unsafe declarations, or hollow definitions. The target is proved; the only remaining `sorry` is the named theorem `exists_split_reduction_factor_thickenings`, with its dedicated node and source/docstring.

3. The split-off factor-thickening statement is a strict lower-level construction: it supplies the open partition and the surjective closed immersions, while the target additionally proves universal homeomorphism by cancellation. Its hypotheses and conclusion are exactly those used by the target, and no duplicate declaration was found in the library or upstream search.

4. The target proof follows the planned route: obtain the factor thickenings, then apply `universalHomeomorphism_of_thickening` to each component. The replaced `Mathlib.AlgebraicGeometry.Limits` import is no longer needed; the new plain proof import is minimal for the changed proof. The unit route remains the same component-lifting step.

5. The DAG records agree with the Lean declarations: the target node depends on the factor-thickening node and the thickening-integrality helper, and the new node records the exact theorem statement, source, proof plan, and module.

Changed in this second reading: no mathematical statements or proofs needed repair; I added this review record and verified the clean compile and delivery metadata.

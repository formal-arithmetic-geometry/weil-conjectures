## What changed

Added the adjunction-unit calculation `baseChange_unit_top` and used it to prove the
three-generator affine tensor formula. Added the smaller tensor-coordinate theorem in
`AffineBaseChangeTensorComparisons.lean`; the main affine base-change theorem remains a
single reduced `sorry` for the locality and affine-chart isomorphism argument.

## Proved and sorry left

Proved `affinePushforward_baseChange_affine_formula`, `affinePushforward_baseChange_algebra`,
and `affinePushforward_baseChange_comp`. The original
`affinePushforward_baseChange` remains sorry; the new
`exists_affineBaseChange_tensorComparisons` is also sorry and is its strictly smaller
comparison component.

## No longer needed

No imports were removed. The original proof plan's relative-spec and open-basis nodes
are not needed by the implemented tensor calculation, but remain dependencies of the
unproved upper isomorphism theorem.

## Where the brief, the DAG or earlier work was wrong

The affine formula can be reduced directly to a tensor-coordinate comparison plus the
adjunction-unit identity; the explicit inverse and affine-local gluing belong only to
the remaining upper theorem.

## New nodes

Added `lem-weil-pbc-affine-base-change-tensor-comparisons`, stated in
`lean/Sheaf/AlgebraicGeometry/AffineBaseChangeTensorComparisons.lean`.

## Second reading by H3

1. Compared the delivered module with the repository version. Existing declaration
signatures are unchanged; the delivery adds only the private unit calculation, the
affine formula proof, and its proof-only import, plus the separately documented split
node/module.

2. Compiled both sandbox modules with `lcompile.py --all`; they compile without errors.
The only remaining `sorry`s are the named upper theorem
`affinePushforward_baseChange` and the split theorem
`exists_affineBaseChange_tensorComparisons`; there are no hollow definitions or
forbidden declarations in the delivered files.

3. The split statement is a strict affine tensor-coordinate reduction, with source,
proof description, dependencies, and Lean declaration recorded in its DAG node. Its
equivalences and generator equations are exactly the data used by the affine formula;
no duplicate of the upper target was introduced.

4. The proof follows the recorded affine route: the private adjunction-unit identity
feeds the generator calculation, while the upper locality/isomorphism argument remains
open. The existing public imports are still needed by declarations; the new comparison
module is imported privately because it is proof-only.

5. The affine formula preserves the unit's tensor-coordinate route, and the algebra and
composition clauses continue to use the existing algebra and pasting nodes. The DAG
proof dependencies and proof origin agree with the Lean proof and the new split node.

Changed during second reading: added this review record only; no Lean statements or
definitions were altered.

## What changed

Proved `AlgebraicGeometry.affine_hom_complex_evaluation` by obtaining the canonical
Hom-complex unit isomorphism from `CategoryTheory.homComplex_unit_iso` and applying a
new intermediate affine direct-image comparison theorem. Added
`Sheaf.AlgebraicGeometry.AffineHomComplexEvaluationD`, whose theorem states the strict
inner comparison and counit compatibility and remains a named `sorry` for the detailed
termwise affine calculation.

## Proved and sorry left

Closed `affine_hom_complex_evaluation`. The new declaration
`affine_hom_complex_d` remains `sorry`; node
`lem-sc-affine-hom-complex-evaluation-d` records its source and proof plan.

## No longer needed

No imports from the original module were removed. The proof uses
`Sheaf.Algebra.Homology.HomComplexUnitIso`; the direct-image and Hom-complex imports
remain needed by the new intermediate statement.

## Where the brief, the DAG or earlier work was wrong

The original four-step proof plan could not be completed in the available time. It was
reduced to the canonical existing unit isomorphism plus a strictly smaller named
intermediate theorem for the affine direct-image calculation.

## New nodes

`lem-sc-affine-hom-complex-evaluation-d` in
`dag/nodes/sec-picard-framework/lem-sc-affine-hom-complex-evaluation-d.json`.

## Earlier second reading (a previous round; superseded)

The second reader should check the canonical unit-isomorphism application, the strictness of the intermediate theorem, and the node signature against the delivered Lean.

## Second reading by Y2

1. The delivered `affine_hom_complex_evaluation` statement is byte-for-byte unchanged
   from the repository version. Its proof obtains `CategoryTheory.homComplex_unit_iso`
   and applies `affine_hom_complex_d`; compilation succeeds.
2. The split-off `affine_hom_complex_d` statement is well-typed and matches its DAG node.
   It is a strict reduction of the target's inner conclusion because the natural
   isomorphism `e` is supplied as an argument; it does not restate the existential
   target. Its proof remains a named `sorry` with source documentation and a node.
3. No definition is hollow and no target hypothesis or conclusion was changed. The
   only remaining `sorry` is `affine_hom_complex_d`.
4. The unit route is preserved: the target still uses the realized Hom-complex unit
   isomorphism step, followed by the affine direct-image comparison node.
5. Imports were pruned for visibility: `HomComplexUnitIso` is now a proof-only import
   of the target module and is no longer publicly re-exported by the split-off module.
   Both sandbox files compile with `lcompile.py --all`.

Changed: moved `Sheaf.Algebra.Homology.HomComplexUnitIso` from a public import in
`AffineHomComplexEvaluationD` to a plain import in `AffineHomComplexEvaluation`.

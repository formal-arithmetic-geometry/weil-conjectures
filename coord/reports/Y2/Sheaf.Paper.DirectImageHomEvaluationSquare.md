## What changed

Completed `AlgebraicGeometry.Etale.DirectImageHomEvaluation.square` using three proved private
helpers in `Sheaf.Paper.DirectImageHomEvaluationSquare`:
`swapped_evaluation_transpose`, `homMap_evaluation`, and `directImageMap_transpose`.
The calculation uses the fixed ordinary etale tensor-Hom adjunction, geometric mate counit,
tensor-comparison naturality, and the existing signed-symmetry involutivity theorem.
Every public declaration signature and every definition body is unchanged.
The final single-file server compile passed cleanly in 8.3 seconds via lcompile.py.
The DAG proof and dependencies now describe that calculation.

Removed seven unused imports and added the proof import
`Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive`.
The import cleanup is recorded in
`coord/changes/Y2-direct-image-hom-evaluation-imports.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.DirectImageHomEvaluation.square`
(node `lem-coef-direct-image-hom-evaluation-square`).
Added zero holes; zero holes remain in the delivered Lean module.
The three private helpers have complete proofs. No new intermediate statement is assumed.

## No longer needed

Removed the imports:

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`

The proof no longer needs the planned general results
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-sf-ringed-derived-tensor-hom-adjunction`, or `def-coef-ringed-tensor-hom-model`.
The ordinary etale definitions already provide the specified comparisons and adjunction.
The two obsolete top-level tool-use approvals for the general ringed comparisons are removed.
The generic scalar-internal-Hom and change-of-rings model theorems are not used either:
this proof works directly with the ordinary etale operations.
The existing statement dependencies are preserved, including the conventions for those notions.
No module is withdrawn; other consumers may still need these generic results.

## Where the brief, the DAG or earlier work was wrong

The six-step mathematical argument is correct. Its planned generic ringed-site interfaces are
unnecessary for this ordinary-etale specialization: the definitions already fix the needed maps.
One additional existing tool, `lem-amb-derived-tensor-symmetry-involutive`, explicitly cancels
the two signed swaps introduced by the library's left-tensor adjunction convention.
The unit route is preserved. The source scan reports zero current Lean importers of the item;
this does not justify withdrawal, and its DAG parent dependency remains intact.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

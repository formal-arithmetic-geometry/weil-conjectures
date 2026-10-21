## What changed

Proved `CategoryTheory.RingedDerivedComparisons.ringedPullbackHomEvaluationComparison`
using private closed-adjunction calculations, naturality of the canonical tensor
comparison, and its existing monoidal lift. Constructed signed evaluation from
Hom-complex composition and canonical evaluation on the coefficient unit. All
existing public signatures and definitions are preserved. Updated the item's node
to record this argument and its actual dependencies. Added
`coord/changes/B5-ringed-pullback-hom-private-proof-context.md` for the private
proof context requested by static preflight. The downstream declaration scan
finds no current Lean consumers; the existing DAG parent keeps the same interface.

The proof imports `RingedDerivedTensorLift`, `RingedHomCompositionModel`,
`HomComplexUnitEvaluationIsIso`, `HomComplexUnitEvaluationComm`, and
`HomTensorSectionNaturality` privately.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.RingedDerivedComparisons.ringedPullbackHomEvaluationComparison`
(node `lem-coef-ringed-pullback-hom-evaluation-comparison`).
No holes added; no holes remain in the delivered module; no split statements.
The required server compile passed without errors or warnings in 25.3 seconds.
The proof uses existing declared dependencies, including
`CategoryTheory.ringedHomComposition_existsUnique`; their proofs are separate items.

## No longer needed

Removed private imports:

- `Sheaf.Paper.RingedTopoiDerivedPullback`;
- `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.

The proof does not invoke `lem-weil-pbc-ringed-topoi-derived-pullback` or
`lem-sfb-ringed-derived-adjoint-lift`: the required normalized lift is already an
input. It uses the edge's canonical comparison directly, so does not invoke
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` separately. These remain statement
dependencies where recorded; no public imports or upstream declarations are removed.

For the signed chain maps, the composition formula and unit-evaluation isomorphism
replace the planned use of `lem-sf-ringed-derived-tensor-hom-adjunction`,
`lem-pc-kflat-resolution`, and `def-pur-derived-internal-hom`. The last definition
still occurs in the public setup, but its representative-independence theorem is
not needed for this proof. These dependencies may remain needed elsewhere; this
delivery withdraws no modules.

Removed obsolete tool approvals for
`lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pc-kflat-resolution`, `def-pur-derived-internal-hom`, and
`lem-sfb-ringed-derived-adjoint-lift`, retaining the other approvals in order.

## Where the brief, the DAG or earlier work was wrong

The old final proof step unnecessarily passed through K-flat resolutions to prove
the stated existence of ordinary signed chain maps. Those maps follow from the
existing uniquely characterized Hom-complex composition and canonical evaluation
on the coefficient unit. The derived compatibility equations are separately
formal consequences of the supplied closed structures and tensor comparison.
The public statement is unchanged, and no unit realization is bypassed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

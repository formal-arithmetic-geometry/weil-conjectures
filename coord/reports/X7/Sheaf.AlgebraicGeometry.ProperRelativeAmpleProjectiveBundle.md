## What changed

Filled `AlgebraicGeometry.isProjectiveBundle_of_isProper_of_relative_ample` in
`Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle`, keeping its statement
and public imports unchanged. The proof follows the existing five-step DAG plan:
properness supplies finite type; `relative_ample_very_ample` gives a positive very
ample power; `veryAmple_finiteType_realization` gives the finite-type bundle and
immersion; `isSeparated_projectiveBundle` and `IsProper.of_comp` make that immersion
proper; `IsClosedImmersion.of_isPreimmersion` closes it using its closed image.
Tensor-power invertibility uses the existing `IsInvertible.tensorPow` instance.

Validation: the final item compiled cleanly through `lcompile.py` (2.1 seconds).

Added private proof imports of `Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization`
and `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isProjectiveBundle_of_isProper_of_relative_ample`
(node `lem-sfb-proper-relative-ample-projective-bundle`).
No holes remain in the item; no holes were added or split off.
The proof uses the existing stated dependencies, whose proofs are separate items.

## No longer needed

Removed the redundant direct proof import of
`Sheaf.AlgebraicGeometry.RelativelyVeryAmple`; its definition remains available through
the required dependencies. No dependency node or module is pruned: all five steps of
the existing plan are used. Public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

None. The dependency statements fit the assembly without changes. Invertibility of
the tensor power is already provided by `IsInvertible.tensorPow` from
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.
The unit route is unchanged; no new statement, definition or DAG node is introduced.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

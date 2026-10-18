## What changed

Added the proof-only import `Sheaf.AlgebraicGeometry.ProjectiveCoordinateBoundaryData`.
The new intermediate theorem `exists_projective_coordinate_boundary_data` packages the
coordinate-polynomial construction, and the target theorem now combines its projectivity and
finite geometric-fibre fields with `isFinite_of_isProjective_of_finite_geometricFibres`.

## Proved and sorry left

The target declaration `AlgebraicGeometry.exists_isFinite_projective_coordinate_boundary` is
proved. One strictly lower intermediate declaration remains sorry:
`AlgebraicGeometry.exists_projective_coordinate_boundary_data` in node
`new-lem-projective-coordinate-boundary-data`. It contains the five geometric construction
steps from the blueprint and is the only remaining hole in this delivery.

## No longer needed

Removed proof-only imports for localization, quasi-finite rings, projective base change, and reduced-induced-subscheme construction from the target module. The target proof now directly uses only the new data theorem and `lem-fin-projective-finite-fibres`; those removed nodes remain encapsulated in the new theorem. The intermediate module exposes no helper definitions; all auxiliary scheme expressions are inlined in its theorem signature.

## Where the brief, the DAG or earlier work was wrong

The original proof plan leaves the coordinate-polynomial construction as several pages of
scheme and commutative-algebra glue. It was not feasible to encode all of that in the target
proof within this item, so it was split into one strictly smaller data theorem whose fields are
exactly the inputs needed by the existing finite-geometric-fibres theorem. The target statement
itself is unchanged.

## New nodes

`new-lem-projective-coordinate-boundary-data` records the intermediate theorem and its
coordinate-polynomial proof plan. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/ProjectiveCoordinateBoundaryData.lean`.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

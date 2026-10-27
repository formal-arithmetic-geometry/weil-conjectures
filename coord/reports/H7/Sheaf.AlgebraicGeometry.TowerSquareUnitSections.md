## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.towerSquare_unit_sections`
using the planned conjugate-unit argument. Private proved helpers evaluate the
pullback compositor and its inverse on iterated unit sections, transport units
along equality of scheme morphisms, and combine these identities by naturality
of presheaf restrictions. The module-square and site-square inverse formulas
are used in the exact transport orientation of their definitions.

All existing public signatures, definitions, and imports are unchanged.
Explicit module-object and test-object parameters prevent expensive kernel
conversion in the final generic calculation. No new public theorem, module,
statement, definition, or DAG node is introduced.

## Proved and sorry left

Original holes: one. Closed:
`AlgebraicGeometry.ProEtale.StrictTower.towerSquare_unit_sections`, node
`lem-cbc-tower-square-unit-sections`.
Added holes: zero. Remaining holes in the item module: zero.
No split-off statements, axioms, or holed definitions.

The final proof compiled in 11.5 seconds before removal of diagnostic output. Final clean compilation and
server delivery checks are recorded by the delivery tool.

## No longer needed

None. Both existing public imports supply definitions used in the statement.
Both planned proof dependencies are used: the strict constant-tower operations
and Mathlib's conjugate-unit identity. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement correction was required. The existing plan closes
the obligation without another decomposition. The equation holds for arbitrary
commutative rings and arbitrary commutative squares, with no open-immersion or
cartesian-square hypothesis. The proof preserves the unit route.

Lean's kernel expensively normalized equality transports when implicit module
and test-object arguments were inferred from the maps. Specifying those
arguments and retaining inverse transport explicitly avoids that conversion;
no shared definition or consumer had to change.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

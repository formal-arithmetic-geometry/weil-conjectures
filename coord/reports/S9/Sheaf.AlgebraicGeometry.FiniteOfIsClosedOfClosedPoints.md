## What changed

Proved `AlgebraicGeometry.finite_of_isClosed_of_closed_points` in
`Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints` without changing its signature
or imports. Bundle the existing assumptions into `IsNoetherian X`, apply Mathlib's
finite irreducible closed cover theorem, choose a generic point of each member,
and use the closed-point hypothesis to identify that member with its singleton.
The finite union is then finite. Updated the node's proof text to name the exact
Mathlib API: maximality of the irreducible cover members is unnecessary.

The proof follows Stacks Tags 0BA8 and 01IS and keeps the unit route. The empty set
is handled by the finite-union theorem, with no nonemptiness assumption added.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.finite_of_isClosed_of_closed_points`
(node `lem-sc-noetherian-closed-points-finite`). No holes remain and none were added.
No decomposition or new intermediate theorem was needed.

Validation: the module compiles through `lcompile.py`; the delivery preflight checks
its axioms. The statement, universes, visibility, and public imports are unchanged.

## No longer needed

None. No imports were added or removed. Both declared dependencies remain used:
`lem-sc-noetherian-closed-subset-finite-components` supplies finite irreducible
closed covers, and `lem-sc-scheme-sober` supplies generic points. They are Mathlib
leaves, so no Sheaf dependency imports are required. No module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The proof needs only a finite irreducible closed cover,
not maximal irreducible components. Mathlib already supplies this exact cover API.
The original assumptions do not automatically synthesize `IsNoetherian X`; the proof
constructs that bundled instance explicitly from those same assumptions.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

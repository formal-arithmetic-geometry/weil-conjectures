## What changed

Proved both theorems in
`Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure`, with their existing
statements and docstrings unchanged. The criterion follows the node's five-step plan:
apply geometric connectedness to the chosen extension; conversely use
`GeometricallyConnected.of_connectedSpace_of_isSepClosed` and
`geometricallyConnected_iff_of_fieldExtension`. Mathlib's
`IsSepClosed.of_isAlgClosed` supplies the field instance. For nonemptiness,
`GeometricallyConnected.connectedSpace_of_subsingleton` packages connectedness over
`Spec k`, and the `ConnectedSpace` instance supplies `Nonempty`.

Removed two redundant proof imports. All existing public imports are preserved.
No definitions, signatures, nodes, or consumers change. The unit record has no
realization attached to this node; its route is preserved by following the given plan.

Searches: LeanFinder for the algebraically closed extension criterion returned no
matching criterion; Loogle for `AlgebraicGeometry.GeometricallyConnected` found the
Mathlib definition and `connectedSpace_of_subsingleton`; msearch grep and local `rg`
found the existing separably closed and field-extension results. Read Stacks
`varieties.tex`, labels `definition-geometrically-connected`,
`lemma-characterize-geometrically-connected` (0387),
`lemma-separably-closed-field-connected-components` (0363), and
`lemma-geometrically-connected-check-after-extension` (054N).

Validation: the module compiles cleanly through `lcompile.py`.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`.
- `AlgebraicGeometry.GeometricallyConnected.nonempty_over_field`.

Both realize `lem-weil-geometrically-connected-algebraic-closure`.
Holes added: 0. Holes left: 0. No split-offs.

## No longer needed

Removed proof imports:

- `Mathlib.FieldTheory.IsSepClosed`: already publicly supplied by
  `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`; the algebraically
  closed to separably closed instance is still used.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its public API was already
  supplied by the preserved public compatibility import
  `Sheaf.AlgebraicGeometry.BaseChangeConventions`; the proofs use Mathlib pullbacks.

No declared dependency node is bypassed. No additional modules or nodes are pruned:
the proof uses the original geometric-connectedness, base-change, field-closure,
separably-closed criterion, extension-descent, and connectedness notions and results.

## Where the brief, the DAG or earlier work was wrong

No mathematical or tool error found. Both substantial dependencies already have
proofs, so no new intermediate statements are needed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Separated the projection records into `StrictEtaleIsomorphicStageProjectionInterfaces` and
added two named intermediate existence statements.  The target theorem now assembles three
coefficient transports and the compact-support projection from those statements; its proof is
complete Lean code.

## Proved and sorry left

Closed `AlgebraicGeometry.strictEtaleIsomorphicStageProjection` (1 of 1 original sorries).
The delivery leaves the two strictly smaller construction obligations as named sorries:

- `AlgebraicGeometry.nonempty_strictEtaleCoefficientTransport_of_bijective`.
- `AlgebraicGeometry.nonempty_strictEtaleTransportProjection_of_equivalences`.

No sorry occurs in a definition.  The interface records and their projection composition are
fully defined.

## No longer needed

No imported dependency was pruned.  The three projection-interface declarations moved from the
target module into `StrictEtaleIsomorphicStageProjectionInterfaces`; the target still publicly
imports that module, so all existing consumers retain the same names.

## Where the brief, the DAG or earlier work was wrong

The original four-step proof plan bundled coefficient transport construction and the geometric
mate assembly into one theorem.  Neither part is available as a proved declaration in the
current library.  The delivery therefore records each as a separate, strictly smaller theorem
and gives a complete assembly proof from them.  No target statement was changed.

## New nodes

- `def-pur-strict-etale-isomorphic-stage-projection-interfaces`
- `lem-pur-strict-etale-isomorphic-stage-transport`
- `lem-pur-strict-etale-projection-from-equivalences`

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

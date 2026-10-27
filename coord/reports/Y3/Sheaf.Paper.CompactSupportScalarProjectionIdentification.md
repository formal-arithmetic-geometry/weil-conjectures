## What changed

Proved `WeilConjectures.PurScalarProjection.inner_domain` from existing integral
constructibility results. The ordinary pullback is identified by its coefficient-map and
left-derived uniqueness equations. The arbitrary tensor presentation is transported through
K-flat representatives to the existing constructible tensor comparison. Its completion
unit is invertible, and the integral residue-Tor criterion supplies the required uniform
finite-Tor predicate. All public signatures and definitions are preserved.

The good-representative helper is reused from IntegralOperationsPreserveConstructible by
a private `import all`; the other local helpers are proved. No projection-formula or
parent coefficient-comparison theorem is used. The DAG Step 2 records this route; the
remaining steps retain their original plan.

## Proved and sorry left

Closed one of the ten original holes: `WeilConjectures.PurScalarProjection.inner_domain`.
Added zero holes and split off zero statements. Nine original holes remain:

- `WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`
- `WeilConjectures.PurScalarProjection.properProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.openProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.realization_existsUnique`
- `WeilConjectures.PurScalarProjection.native_scalar_identification`
- `WeilConjectures.PurScalarProjection.gamma_identification`
- `WeilConjectures.PurScalarProjection.diagram_projection`
- `WeilConjectures.PurScalarProjection.ordinaryCompletedSquare`
- `WeilConjectures.PurScalarProjection.compactSupportScalarProjectionIdentification`

## No longer needed

For the replaced domain argument, the item no longer needs
`lem-pur-completed-operation-tower-substitution`, `lem-sf-pullback-tor-amplitude`, or
`lem-sf-tensor-ctf`; their former Step 2 use is replaced by the constructibility and
residue-Tor route. They were not Lean imports of the original item. No module is
withdrawn and no existing public import is removed. The other original proof dependencies
remain needed by the nine unproved declarations.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing parent compact-support coefficient-comparison
square is not a permissible shortcut: its planned proof depends on this item. The proof
here does not use it or the projection-formula theorem. The original finite-level domain
plan was longer than the available integral constructibility and residue-Tor route.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

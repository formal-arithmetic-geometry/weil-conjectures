## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.kummerParameterSquare` in
`Sheaf.Paper.KummerParameterizedTerm`. Unfold only the full parameter map, reassociate,
apply `coefficientParameterProjectionCommutes`, reassociate again, and use `h : i ≫ q = s`.
The projection equation is already proved by `pullback.lift_snd` in
`Sheaf.Paper.ProfiniteCoefficientLinearization`. All statements, definitions, structures,
public imports and the geometric comparison map are preserved.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.CondensedRing.kummerParameterSquare`
(node `def-sfb-kummer-parameterized-term`).
No holes remain in the item. No holes were added or split off.

## No longer needed

None. The existing node has no proof dependencies to prune. Both public imports
remain necessary for the existing structure and geometric map; no proof import is added.
The square requires no finiteness, nonemptiness or geometric hypothesis on P.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The stale rework row names an old quarantine path,
but the current item source is present under `lean/Sheaf/Paper/`; the rework-done
record confirms restoration. This delivery uses that current source and preserves
its Lean attachment and dependencies.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

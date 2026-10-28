## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_ordinary_kummer_boundary` in
`lean/Sheaf/Paper/FiniteP1OrdinaryKummerBoundary.lean`.  The proof obtains the normalized
ordinary projective-line Chern specification from
`Etale.projectiveLineTraceDatum.chern_spec` and applies the finite site-comparison
intermediate theorem.  Added the proof-only import
`Sheaf.Paper.FiniteP1OrdinaryKummerBoundaryCore`.

The intermediate theorem is stated in
`lean/Sheaf/Paper/FiniteP1OrdinaryKummerBoundaryCore.lean`; it isolates the scalar
ordinary Chern-class specification as the input to the finite Kummer boundary
comparison.  Its proof remains a named split-off obligation with its own DAG node.

## Proved and sorry left

Closed the item theorem
`AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_ordinary_kummer_boundary`.

The delivery adds one split-off `sorry`,
`AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_ordinary_kummer_boundary_of_class`,
recorded by node `lem-sfb-finite-p1-ordinary-kummer-boundary-core`.

## No longer needed

No imports were removed.  The item proof itself uses only the finite Kummer boundary
expression and the new scalar-class comparison theorem; the older proof-plan nodes
remain dependencies of that split-off theorem and are therefore still needed.

## Where the brief, the DAG or earlier work was wrong

Nothing in the brief or the existing statements was changed.  The proof makes the
DAG's scalar-class step explicit as a strictly simpler intermediate obligation before
packaging its result as `FiniteKummerBoundary`.

## New nodes

`lem-sfb-finite-p1-ordinary-kummer-boundary-core` records the theorem
`finiteP1_ordinary_kummer_boundary_of_class` and its source-backed proof plan.  The
module is `lean/Sheaf/Paper/FiniteP1OrdinaryKummerBoundaryCore.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteP1OrdinaryKummerBoundary": "74d53b62f9625bf804f0e52a6568406285eb9c02", "Sheaf.Paper.FiniteP1OrdinaryKummerBoundaryCore": "2e559e6e894c78312947fab09d976cfa52c59801"}, "results": {}, "time": "2026-10-28T08:14:57+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

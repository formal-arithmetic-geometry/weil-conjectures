## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.finite_unit_push` by
specializing the normalized finite coefficient-unit square to the identity local
arrow and cancelling the finite realization unit isomorphism. Added
`Sheaf.Paper.DiagonalFiniteUnitPushCore`, which states the uncancelled normalized
square as the remaining named proof step and is imported privately through the
public dependency chain.

## Proved and sorry left

Closed the `finite_unit_push` hole. One strictly lower normalization hole remains
in `finite_unit_push_square` in
`Sheaf.Paper.DiagonalFiniteUnitPushCore` (node
`lem-diagonal-finite-unit-push-square`).

## No longer needed

The proof does not use the direct proof dependency `sk-lem-geo-p1-cohomology`
listed by the original node; the finite adjunction endpoint is already provided
by `DiagonalCoefficientUnitPush`. No other declared dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted the uncancelled single-object normalization
as a separately named Lean step. It is now recorded as the strict lower node
`lem-diagonal-finite-unit-push-square`; the top-level theorem is a real categorical
cancellation from that step.

## New nodes

`lem-diagonal-finite-unit-push-square` is stated in
`lean/Sheaf/Paper/DiagonalFiniteUnitPushCore.lean` and recorded in the matching DAG
node. Its proof follows the supplied `FinitePushSquare.derived.normalization`,
ordinary unit normalization, and `hcanonical` equation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalFiniteUnitPush": "eb8e124f6fb3e3046fea4786d72a79c1efe3dcb2", "Sheaf.Paper.DiagonalFiniteUnitPushCore": "40de7e52cdb0bc3a45811a3d4bbe6381bcf272b4"}, "results": {}, "time": "2026-10-28T08:20:47+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Added the split-off module `Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPathRealized`, whose
strictly weaker statement compares the two route composites after intrinsic realization and
composition with the target comparison. The requested theorem now applies faithfulness of the
intrinsic full inclusion and cancels that target isomorphism. The item module imports only the
coordinates and the split-off realized statement.

## Proved and sorry left

The declaration `WeilConjectures.sixFunctorProjectionFinite_right_left_path` is proved. One
strictly simpler intermediate declaration remains sorry:
`WeilConjectures.sixFunctorProjectionFinite_right_left_path_realized`, node
`lem-sf-finite-base-change-right-left-path-realized`.

## No longer needed

The direct imports of `Sheaf.Paper.FiniteProjectionExchangeTransposes` and
`Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality` are not needed by the item module after
moving the route calculation to the realized intermediate statement. No proof dependency is
pruned beyond replacing the original direct calculation dependencies with the new intermediate
node.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted the endpoint realization and comparison cancellation
needed to turn the fixed-scalar diamond equality into equality in the finite constructible
category. The split-off statement records that missing coordinate calculation explicitly; the
parent proof then performs the faithful-functor cancellation in Lean.

## New nodes

`lem-sf-finite-base-change-right-left-path-realized` is the realized route equality described
above. Its Lean declaration is in
`lean/Sheaf/Paper/ProjectionFiniteBaseChangeRightLeftPathRealized.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath": "ff1bd5ff63eca7d417fea07578d2853cc3b2b03f", "Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPathRealized": "95da451d0d33b657afed90f000964df5650bc089"}, "results": {}, "time": "2026-10-28T09:44:16+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

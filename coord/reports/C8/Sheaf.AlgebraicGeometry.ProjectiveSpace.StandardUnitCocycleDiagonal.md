## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.standardUnitCocycle_diagonal_normalization`
in its existing module without changing its signature or imports. Both diagonal units equal
one by their repeated-index cocycle equations and cancellation. For the standard transition
cocycle, restriction back to the diagonal overlap avoids transporting sections across equal
opens; functoriality makes the composite restriction maps identities. Updated the docstring
and the node's proof route to match. Corrected the docstring's blueprint identifier.
The proof compiled in 4.4 seconds; the axiom probe also passed. Delivery reruns
compilation after explicitly referencing the retained unused hypotheses for the linter.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProjectiveSpace.standardUnitCocycle_diagonal_normalization`
(node `lem-sfb-projective-standard-unit-cocycle-diagonal`).
No holes remain in the item, no holes were added, and no statements were split off.

## No longer needed

Removed no imports. The proof does not need node
`lem-sfb-projective-standard-unit-cocycle-off-diagonal` or its module
`Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal` as a proof dependency;
removed that edge from this node. That module is still needed by the parent normalization
argument and is not withdrawn. The hypotheses `hr` and `hoff` are unnecessary for this diagonal
calculation, but the statement is preserved verbatim. The standard transition cocycle
`lem-pc-twist-cocycle` remains the sole proof dependency.

## Where the brief, the DAG or earlier work was wrong

The old plan unnecessarily cited the off-diagonal existence theorem and proposed using a pair
and its reverse. Repeating all three indices suffices for each diagonal identity. The unit
route is preserved; no shared definition, statement, attribute, or import changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleDiagonal": "db6762e893be32833d0221811ef51e8019992755"}, "results": {}, "time": "2026-10-27T23:36:10+0800", "transitive": 0, "version": 1}
```

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

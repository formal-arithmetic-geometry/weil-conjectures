## What changed

Added `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalTrace`, a split-off geometric
local-trace exchange theorem.  The assigned theorem now applies that core and proves the
remaining arbitrary-arrow wrapper by naturality of the inverse-image compositors and
`ordinaryFiniteUnitPullback_comp`, followed by the supplied equations `hkS` and `hkT`.
The item imports the new core and `Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp`.

## Proved and sorry left

`AlgebraicGeometry.Etale.vectorIntegration_baseChange_local_unit` is proved.  One sorry is
left in `AlgebraicGeometry.Etale.vectorIntegration_baseChange_local_trace`, whose statement
is the strictly simpler geometric core and whose node is
`lem-pur-vector-integration-base-local-trace`.

## No longer needed

The assigned theorem's proof uses only the new geometric-core node and
`lem-amb-ordinary-finite-unit-pullback-comp`; the seven original geometric proof dependencies
are no longer direct dependencies of this module and were removed from its node proof plan.
No imports were removed from the pre-existing module.

## Where the brief, the DAG or earlier work was wrong

The DAG's single geometric step combines the Cartesian exchange, affine counit base change,
and arbitrary-arrow substitution into one theorem-sized proof.  The available declarations
support the categorical substitution independently, but the geometric exchange itself is a
separate substantial statement.  It was split into a strictly simpler local-trace theorem;
the assigned theorem then combines it with a complete categorical calculation.

## New nodes

`lem-pur-vector-integration-base-local-trace` records the split geometric local-trace
exchange and is stated in
`lean/Sheaf/AlgebraicGeometry/VectorIntegrationBaseChangeLocalTrace.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalTrace": "29cb6a319ec96658e650cba3157255ffc5ecc26e", "Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit": "8ce2b603a6e61328a24881e84cf65f33cb8cc925"}, "results": {}, "time": "2026-10-28T08:19:23+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

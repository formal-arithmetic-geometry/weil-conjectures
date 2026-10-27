## What changed

The assigned module remains statement-compatible and compiles.  The proof plan now
extracts the complete-standard-chart calculation as the strict subproblem
`lem-sfb-proj-scalar-extension-twist-chart-basic`, with a dedicated module and named
statement.  The original arbitrary-open theorem is left available for the subsequent
sheaf-restriction proof.

## Proved and sorry left

- `AlgebraicGeometry.Proj.scalarExtension_twistMap_basicOpen_bijective`: one `sorry`
  remains; the arbitrary-open restriction step is not closed here.
- Added `AlgebraicGeometry.Proj.scalarExtension_twistMap_chart_bijective`: one
  `sorry` remains for the complete-chart homogeneous-localization calculation.

## No longer needed

None.  The original proof dependencies remain needed by the extracted chart calculation.

## Where the brief, the DAG or earlier work was wrong

The original node combined the complete standard-chart calculation with the arbitrary
subopen sheaf-restriction step in one theorem.  These are separate obligations: the
chart calculation is a strict local subproblem and is recorded as a new node so that
it can be proved independently before the restriction argument.

## New nodes

- `lem-sfb-proj-scalar-extension-twist-chart-basic`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart": "5f4d1dbfd56e68cd2272f1f4a94bbb3b075f3f24", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic": "5284667770bb4cf8e299d91a7e2a57152f470115"}, "results": {}, "time": "2026-10-28T05:16:03+0800", "transitive": 0, "version": 1}
```

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

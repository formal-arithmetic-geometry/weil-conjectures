## What changed

Proved `WeilConjectures.sixFunctorProjectionFinite_left_tensor_transport` without
changing its statement. Added a private proof import of
`Sheaf.Paper.FinitePullbackCompositionFixedCoordinates` and private proved helpers
for the unary square, coefficient-unit cancellation, tensor naturality, and support
naturality. Updated the existing node to record this proof dependency.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.sixFunctorProjectionFinite_left_tensor_transport`
(`lem-sf-finite-base-change-left-tensor-transport`). No holes added or split off;
no `sorry` remains in the delivered module. The proof uses the existing theorem
`CompactSupportFiniteProjection.pullbackComposition_fixed_coordinates`, whose own
proof remains an independent project obligation.

## No longer needed

None. All original dependencies remain needed through the coordinate definitions.
No imports, modules, or nodes were withdrawn.

## Where the brief, the DAG or earlier work was wrong

The unary normalized compositor compatibility already has the declaration
`CompactSupportFiniteProjection.pullbackComposition_fixed_coordinates`. Reusing it
avoids another split of the pullback-square calculation. No statement or definition
repair was required; the unit route is preserved.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ProjectionFiniteBaseChangeLeftTensorTransport": "b7a9bdef67ca50505db962f8b1104a6882b9fc49"}, "own_failed": ["Sheaf.Paper.ProjectionFiniteBaseChangeLeftTensorTransport"], "results": {}, "time": "2026-10-28T14:55:49+0800", "transitive": 0, "version": 1}
```

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Restored `Sheaf.Paper.NativeWeilScalarCounitData` from its quarantine copy and repaired
its compile-time performance. The module now disables the expensive private-module
linter and locally marks the general algebraically closed coefficient `stageSystem`
irreducible. The `ScalarNormalization.shift` field uses explicit `HasShift` and
`CommShift` instances so that this performance repair remains type correct. The public
structures, fields, and declarations are unchanged.

## Proved and sorry left

The module has zero `sorry` declarations. All existing declarations, including
`fiberSourceFinite`, `fiberTargetFinite`, `fiberSourceQc`, `fiberTargetQc`,
`rawSourceFinite`, `rawTargetFinite`, `rawSourceQc`, `rawTargetQc`,
`fiberRelativeSeparated`, `fiberRelativeFinite`, `fiberRelativeQc`, `CounitData`,
`FrobeniusNormalization`, and `ScalarNormalization`, compile successfully.
No new `sorry` was added.

## No longer needed

None. The module's existing imports and DAG dependencies remain needed by its public
signatures.

## Where the brief, the DAG or earlier work was wrong

The rework entry correctly identified a slow definition, but the expensive unfolding
was the coefficient `stageSystem` used throughout the dependent structures. Marking it
locally irreducible, together with explicit shift instances in the final field, reduces
the standalone compile from over the 60-second limit to about 40 seconds. No statement,
unit route, or DAG dependency was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilScalarCounitData": "fce6c5f8e0bf6f76331411b276d64418403b047e"}, "results": {}, "time": "2026-10-28T07:39:37+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

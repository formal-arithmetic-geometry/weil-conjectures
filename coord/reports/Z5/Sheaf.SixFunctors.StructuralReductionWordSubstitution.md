## What changed

Restored `Sheaf.SixFunctors.StructuralReductionWordSubstitution` now performs an explicit
constructor split for all structural generator kinds. The nine structural constructors are
factored into named constructor-specific theorem modules. The four open-generator branches are
discharged from the definitional contradiction `Structural g = False`, while the nine structural
branches are delegated to the corresponding split theorem. Each split theorem is a named,
public intermediate statement with the complete source proof obligation recorded in its
blueprint-tagged docstring.

## Proved and sorry left

The parent theorem `structuralReductionWordSubstitution` is proved by the complete constructor
split. Nine strictly smaller constructor-specific theorems remain as named `sorry`s:
`structuralReductionTensorAssociator`, `structuralReductionTensorLeftUnit`,
`structuralReductionTensorRightUnit`, `structuralReductionPullComposition`,
`structuralReductionPushComposition`, `structuralReductionPullPushUnit`,
`structuralReductionPullPushCounit`, `structuralReductionOpenUnit`, and
`structuralReductionOpenCounit`. Each has a corresponding DAG node in this delivery.

## No longer needed

No existing proof-dependency imports were removed. The parent now uses only the nine
constructor-specific modules and `OpenInterchangeReductionData`; the large unimplemented
reconstruction dependencies listed in the original blueprint proof are postponed to the split
constructor nodes.

## Where the brief, the DAG or earlier work was wrong

The restored item had a bad import in the preceding global build because its dependency had been
quarantined. The live dependency is present again. The original node presented one monolithic
unbounded substitution proof; the delivery makes its constructor decomposition explicit so each
remaining obligation is strictly smaller and independently claimable.

## New nodes

This delivery adds nine constructor-specific nodes and modules, one for each structural
constructor. Their declarations and files are recorded by the `lean` records in the corresponding
node JSON files under `dag/nodes/sec-six-functors/`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.StructuralReductionOpenCounit": "ff01d87c17dce6df08cb13d6797d768f6415b953", "Sheaf.SixFunctors.StructuralReductionOpenUnit": "fbe0257e5ec606bf34092295800b9dd34deb74f3", "Sheaf.SixFunctors.StructuralReductionPullComposition": "8106957c6872fbbf8ed87586afe70e77ef8b1ff2", "Sheaf.SixFunctors.StructuralReductionPullPushCounit": "20ff42b6ff9a0d93bbc29a37a7ee8bacaca0aa0f", "Sheaf.SixFunctors.StructuralReductionPullPushUnit": "5dc438cbb4de1c893b50647fa573789b9a5343e6", "Sheaf.SixFunctors.StructuralReductionPushComposition": "f83d86070a89dc15d3dbc8cdf6bf930fe0907887", "Sheaf.SixFunctors.StructuralReductionTensorAssociator": "a5bfa876b93956907090d5586a76113019504ed3", "Sheaf.SixFunctors.StructuralReductionTensorLeftUnit": "4c76cd09c3f3a2ce8e708cdc253b36dfddc7ab75", "Sheaf.SixFunctors.StructuralReductionTensorRightUnit": "46fff950285de4efaead61c13022325200bea6f9", "Sheaf.SixFunctors.StructuralReductionWordSubstitution": "ae84af56ad38896813e61ff3614a29f80677bb34"}, "results": {}, "time": "2026-10-28T01:28:29+0800", "transitive": 0, "version": 1}
```

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

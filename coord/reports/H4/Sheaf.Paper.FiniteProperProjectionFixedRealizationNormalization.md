## What changed

Added the lower coordinate projection theorem in
`Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalizationCore` and used it to
prove `properComponent_fixed_realization_normalization`.  The proof applies the
adjunction transpose counit formula and the published right-derived lower-star
projection/counit identity.  The parent module imports the new lower module.

## Proved and sorry left

The assigned theorem `properComponent_fixed_realization_normalization` is proved.
The lower theorem `properComponent_fixed_realization_coordinate_projection` remains
one split-off `sorry`, with node
`lem-sf-finite-proper-projection-fixed-realization-normalization-core`.

## No longer needed

The proof does not use the old direct proof dependencies as separate proof steps;
they are used only by the split-off coordinate theorem.  No imported module was
removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof omitted the intermediate coordinate projection equation
needed before applying the generic adjunction counit identity.  This delivery records
that equation as a strictly simpler lower statement.

## New nodes

`lem-sf-finite-proper-projection-fixed-realization-normalization-core` records the
coordinate projection equation and its remaining proof obligation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization": "dd25e0772ac0122e55cc904440d0515146db3120", "Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalizationCore": "f4dc0688ee520a488c085415895a99adc0386731"}, "results": {}, "time": "2026-10-28T09:39:53+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

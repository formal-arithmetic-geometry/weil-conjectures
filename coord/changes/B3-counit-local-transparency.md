# derivedPullbackComposition_counit_normalization

## Reason

Keep definitional elaboration from expanding the tensor and derived pullback
constructions during the proof. The assigned signature and public imports stay
identical; the helper combineCounit is private, proved, and used only in a proof.

## Old

No local reducibility override in the assigned module.

## New

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback derivedPullback
```

These attributes are local to the namespace and change neither the declarations
nor their exported reducibility. No definition, statement or visibility changes.
Static preflight conservatively flags the attribute command as an interface edit.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | B3 | Proof elaboration only; identical public signature. |

No downstream adaptation is required because the attributes are local.
The new TensorPullbackCompositionHomotopyCounit module exports the single
intermediate theorem in its new node and is imported only for the assigned proof.
Its hole is a named theorem, never definition data.

## Status

landed 20261014T063813-L-2812622 2026-10-14 (merge of deliver/B3/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization)

## What changed

Proved `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates` by constructing the two natural transformations appearing in the statement and proving their equality by extensionality on K-injective representatives. Naturality is discharged from the naturality of the three direct-image comparisons, the fixed-scalar and intrinsic compositor maps, and functoriality of the relevant direct-image functors. A private derived-category extensionality lemma transports equality from K-injective representatives to every derived object.

Split the K-injective representative calculation into the new public theorem `sfIntrinsicDirectCompositorCoordinates_kInjective` in `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective`; its body remains a named lower-stage `sorry`. Both modules compile in import order with `lcompile.py`.

## Proved and sorry left

- Closed the original hole in `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates`.
- Added one strictly lower hole, `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates_kInjective`, for the K-injective representative equality used by the extensionality argument.

The delivered modules contain no other `sorry`s and no sorry occurs in a definition.

## No longer needed

- Removed the exploratory private `import all Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization` from both modules; the delivered proof uses only the existing public imports and the split theorem.
- The original public imports and all existing proof dependencies remain available. No existing source module or declaration was changed.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan treated the full representative calculation and transport to arbitrary derived objects as one step. The categorical transport is short once the representative equality is isolated, so the former is split into a strictly simpler K-injective theorem and the parent is proved from it. The target statement and all its binders are unchanged.

## New nodes

- `lem-sf-intrinsic-direct-compositor-coordinates-k-injective`, attached to `Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective.sfIntrinsicDirectCompositorCoordinates_kInjective`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicDirectCompositorCoordinates": "21f057668ad96c6c057bcea653ef16a81a96437c", "Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective": "231fb76f87677a8d195d52af066821c8205793f8"}, "results": {"Sheaf.Paper.SystemFiniteCompositorCoordinates": {"hash": "495fb6ec9967ba37ba48ae5a7aa7b4a8ecdb6665", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T01:29:50+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.integral_site_pullback_integer_endpoint_inverse_image`.
The proof unfolds `Scheme.proEtaleConstantInverseImageMap`, applies
`Adjunction.homEquiv_counit`, and closes the remaining equality by the definitional
identification of `proEtaleSheafAdjunction` with `upperStarLowerStarAdjunction`.
Removed the unused public import `WeilConjectures.ConstructibleSheaf.Defs`.

## Proved and sorry left

Closed the sole `sorry` in
`AlgebraicGeometry.ProEtale.SpTowerClasses.integral_site_pullback_integer_endpoint_inverse_image`.
The delivered module has zero remaining `sorry`s and adds none.

## No longer needed

The proof does not use `WeilConjectures.ConstructibleSheaf.Defs`, so that public import
was removed. The proof uses only the existing declaration recorded by
`def-weil-proetale-inverse-image`; no other proof dependency is needed and no module or
node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The split node had an empty proof plan. Its statement is directly the adjunction
counit formula built into `proEtaleConstantInverseImageMap`; after unfolding, the two
adjunction presentations are definitionally equal. No statement or definition was
changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralSitePullbackIntegerEndpointInverseImage": "a3fe05841ece2d65668a5549244452f73128c8ab"}, "results": {"Sheaf.Paper.IntegralSitePullbackIntegerEndpoint": {"hash": "cd793f4311d81e32553b59c83c86ab41de86328c", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T09:23:19+0800", "transitive": 0, "version": 1}
```

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

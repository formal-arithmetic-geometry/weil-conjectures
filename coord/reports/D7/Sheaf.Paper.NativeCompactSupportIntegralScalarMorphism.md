## What changed

Added proof-only imports and a complete assembly proof for
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_morphism`.
The proof obtains the natural transformation and its `b`/comparison/`d`
factorization from `native_integral_scalar_morphism_exists`, then obtains the
explicit six-arrow component from
`native_integral_scalar_morphism_normalization` and unfolds `IntegralComponent`.
The two strictly smaller obligations are in the new modules
`NativeCompactSupportIntegralScalarMorphismExistence` and
`NativeCompactSupportIntegralScalarMorphismNormalization`.

## Proved and sorry left

Closed the original `native_integral_scalar_morphism` sorry (1 of 1). The
parent proof is complete and compiles. Added two named split-off sorries:

- `native_integral_scalar_morphism_exists`, node
  `lem-sf-native-integral-scalar-morphism-existence`, for existence of `tau`
  and its outer-factor decomposition;
- `native_integral_scalar_morphism_normalization`, node
  `lem-sf-native-integral-scalar-morphism-normalization`, for the six-arrow
  `IntegralComponent` calculation for a given factorized `tau`.

## No longer needed

None. The original module had only its public data import; the normalization
proof import is needed by the completed proof. The parent proof uses the two
new nodes and no unused proof dependency imports.

## Where the brief, the DAG or earlier work was wrong

The original node's four prose proof steps are too large to realize directly
from the available declarations. The delivery preserves their mathematical
content by separating the construction into the natural-transformation
factorization and the component calculation, then combines them in Lean.
No target statement or existing definition was changed.

## New nodes

`lem-sf-native-integral-scalar-morphism-existence` and
`lem-sf-native-integral-scalar-morphism-normalization` are new declaration-level
proof obligations, each strictly smaller than the parent: the first omits the
six-arrow normalization, and the second assumes the natural transformation and
its factorization. They are stated in the corresponding new modules and their
DAG records carry the source and proof decomposition.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism": "4ec1e73c82e697b70c8103c0abb6839f055f51ab", "Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence": "c4b1893a934feec34687c4f683c2d408b2c0df21", "Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization": "e16718a302e3af74d29f30bb5bad2504626e555f"}, "results": {}, "time": "2026-10-28T04:21:13+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

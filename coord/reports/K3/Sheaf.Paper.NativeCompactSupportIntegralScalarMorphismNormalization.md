## What changed

Marked `native_integral_scalar_morphism_normalization` as
`STATEMENT-DISPUTED` and restored the module to its delivered interface. No
proof term or public signature was weakened.

## Proved and sorry left

No sorries were closed and no new sorries were added. The existing sorry in
`native_integral_scalar_morphism_normalization` remains, attached to node
`lem-sf-native-integral-scalar-morphism-normalization`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The node's hypotheses provide only
`map (tau.app K) = b.hom ≫ comparison ≫ d.hom` for existential isomorphisms
`b` and `d`. They do not identify `b` or `d` with the prescribed canonical
outer composites in the conclusion. For any automorphism `u` of the middle
object, replacing `b` by `b ≫ u` and `d` by `u⁻¹ ≫ d` preserves the hypothesis,
while changing the unconstrained factors. Therefore the canonical six-arrow
equality cannot follow from the stated assumptions. A correct statement needs
normalization hypotheses for the outer factors (or must quantify the factors
and record their normalization).

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization": "5020b6713340f8e964cc31feaaff6c3b4738ae7e"}, "results": {}, "time": "2026-10-28T06:52:35+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

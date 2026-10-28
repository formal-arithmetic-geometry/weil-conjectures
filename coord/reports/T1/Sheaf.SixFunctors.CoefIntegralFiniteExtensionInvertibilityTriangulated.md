## What changed

Added `Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp`, splitting off the
strictly simpler derived-quotient precomposition triangulatedness assertion. The item now
imports that theorem and proves `comparison_invertibility_triangulated_isTriangulated` by
`Functor.isTriangulated_of_precomp`; the existential wrapper remains proved unchanged.

## Proved and sorry left

`comparison_invertibility_triangulated_isTriangulated` and
`comparison_invertibility_triangulated` are proved. One strictly simpler theorem remains a
`sorry`: `comparison_precomp_triangulated` in
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp`, node
`lem-sf-integral-finite-extension-triangulated-precomp`.

## No longer needed

No declared proof dependency was removed. The proof uses only the new precomposition node
and the derived quotient's standard localization infrastructure.

## Where the brief, the DAG or earlier work was wrong

The original module's upper theorem had no usable direct declaration for the full
triangulatedness proof. The reduction through `Functor.isTriangulated_of_precomp` makes the
remaining chain-level obligation explicit as a strictly simpler statement.

## New nodes

`lem-sf-integral-finite-extension-triangulated-precomp` records the derived-quotient
precomposition obligation and is stated in
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated": "924fd29e185b6b2686ba72f74fb9e2442d3edd13", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp": "6d6e2553b7850f9cd2f4d39f37d8d478dc9b7c5a"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility": {"hash": "bc6d2cee3ee60dda8a76937e86a1e840f78ccc55", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T09:58:34+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

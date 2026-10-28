## What changed

Proved `AlgebraicGeometry.Scheme.sfIntrinsicConjugateComparisonTransport` in
`Sheaf.Paper.IntrinsicConjugateComparisonTransport`, with its statement unchanged.
The proof checks the ordinary pullback compositor under the coefficient equivalences,
derives that square by exact localization, identifies each inverse direct-image
comparison as the mate of its pullback square, and applies mate pasting. The
left-derived and exact-derived fixed-coefficient conjugates agree by the existing
adjunction identification. Cancelling the two forward comparisons and applying
`sfIntrinsicDirectComparisonTransport` gives the asserted coordinate equation.

Added proof imports of `Sheaf.Paper.FiniteDirectCounitFixedRealizationTransport`
(using its proved private counit and adjunction-identification helpers),
`Sheaf.AlgebraicGeometry.SfIntrinsicDirectImageUnitNormalization`,
`Sheaf.CategoryTheory.DerivedExactSquareComposition`, and
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`.
Updated the item's node proof, proof dependencies, and proof origin to record this
argument. No shared definition, public signature, or other module was changed.
The complete module compiled without errors or warnings in 27.7 seconds through
`lcompile.py`. The updated dependencies contain no path back to this node.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.sfIntrinsicConjugateComparisonTransport`
(node `lem-sf-intrinsic-conjugate-comparison-transport`).
There are zero holes left in the item and zero holes added or split off.
The proof still uses the existing stated dependency
`AlgebraicGeometry.Scheme.sfIntrinsicDirectComparisonTransport`; its own proof is
outside this delivery.

## No longer needed

None. The original public imports and declared dependencies remain needed.
No modules or nodes are withdrawn. No new unproved transport obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

The previous node's mate-transport step did not specify the normalization needed to
identify the chosen derived direct-image comparison with a mate. The existing
all-complex unit normalization and the proved private derived counit-square helper
supply it. The revised proof records this detail and the exact-localization
composition theorem; the statement and the unit route are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicConjugateComparisonTransport": "1a43314c242bd841a51b72c17060430c16f8272f"}, "results": {"Sheaf.Paper.IntrinsicDirectCompositorCoordinatesMatePasting": {"hash": "8c9474b340c9aeefcaae9125126369c1ce28a798", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T14:43:44+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

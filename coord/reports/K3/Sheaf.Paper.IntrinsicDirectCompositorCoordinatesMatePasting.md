## What changed

The two target theorems now compile.  The proof uses two split-off transport statements: one
for the normalized direct-image comparison square and one for the intrinsic conjugate before
the final comparison.  The original module keeps only the ambient coordinate definition and
the short composition proofs.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates_ambient_normalization`
- `AlgebraicGeometry.Scheme.sfIntrinsicDirectCompositorCoordinates_ambient_to_intrinsic`

Split off with `sorry`:

- `AlgebraicGeometry.Scheme.sfIntrinsicDirectComparisonTransport`
- `AlgebraicGeometry.Scheme.sfIntrinsicConjugateComparisonTransport`

## No longer needed

Removed the unused import of `Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization` and
the copied private transport-mate helper declarations.  The proof does not use the old private
helper route or its ambient-normalization dependency.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the naturality identities needed to move the section-normalized
derived direct-image comparisons through the realization equivalences.  It also treated the
left-derived and exact-derived intrinsic adjunctions as definitionally equal; they require the
separate conjugate-coordinate statement recorded in the second split node.

## New nodes

- `lem-sf-intrinsic-direct-comparison-transport`
- `lem-sf-intrinsic-conjugate-comparison-transport`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicConjugateComparisonTransport": "412c8e1c817834fb7465b50badbf1d1530e178b6", "Sheaf.Paper.IntrinsicDirectComparisonTransport": "a1ea1ed97547824f15db75067ecb449a3a2d89d5", "Sheaf.Paper.IntrinsicDirectCompositorCoordinatesMatePasting": "8c9474b340c9aeefcaae9125126369c1ce28a798"}, "results": {"Sheaf.Paper.IntrinsicDirectCompositorCoordinatesKInjective": {"hash": "e5871106a2f9e0aacfb79ca831711d4c455b18b8", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T10:05:13+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

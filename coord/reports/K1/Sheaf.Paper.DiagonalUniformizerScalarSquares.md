## What changed

Restored `Sheaf.Paper.DiagonalUniformizerScalarSquares` from its quarantined source and
replaced its mate-invertibility `sorry` with a completed finite-free rank-one
resolution argument. Added `Sheaf.Paper.DiagonalScalarSquareTypes`,
`Sheaf.Paper.DiagonalUniformizerPointResolution`, and
`Sheaf.Paper.DiagonalUniformizerMateComparison`; these provide transparent aliases,
the actual two-term quotient resolution, and the normalized square/mate comparison.
The item now proves all three declarations without `sorry`.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_uniformizer_restriction_mate_isIso`,
the only `sorry` in the item. The existing square and packaging declarations remain
proved. The three new support modules add no `sorry`.

## No longer needed

The repaired route no longer imports the abstract perfect-model theorem or the former
normalization modules used only by that route: `Sheaf.Paper.NormalizedScalarRestrictionPush`,
`Sheaf.Paper.InternalPullNormalizationExistence`,
`Sheaf.Paper.ComapUpperStarIsoMate`,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, and
`WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction`. The restored
coefficient-diagram dependency remains required by the public interfaces.

## Where the brief, the DAG or earlier work was wrong

The prior red-build drop quarantined this item together with its coefficient-diagram
imports, so the current rework requires restoring that source before proving it. The
former abstract perfect-model route was replaced below the unit by the concrete
rank-one finite-free quotient resolution; the corresponding DAG route and proof
 dependencies are recorded in the delivered node copies.

## New nodes

`def-diagonal-scalar-square-types` records the transparent aliases used to keep the
specialized interfaces compact. `lem-diagonal-uniformizer-point-resolution` proves
the two-term condensed rank-one resolution of the actual quotient. `lem-diagonal-finite-
resolution-scalar-mate` proves normalized square existence and mate invertibility for a
rank-one finite-free point resolution. The change record is
`coord/changes/C6-diagonal-scalar-square-types.md`.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 6 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalScalarSquareTypes": "614d016d27a54c0edb8346c2e254cdc6872d6ad0", "Sheaf.Paper.DiagonalUniformizerMateComparison": "fed1980f938ce9a3e6a15cd23a96577eb01cd8b7", "Sheaf.Paper.DiagonalUniformizerPointResolution": "14e0ec092d2d487d3986453d749389e3a2aed057", "Sheaf.Paper.DiagonalUniformizerScalarSquares": "463dddecd0c785dca4760046dc81f54c4205c2a9"}, "results": {"Sheaf.Paper.DiagonalClosureScalarFrame": {"hash": "4bbf2151fba128bbc5025f8ca674757aaffebd06", "status": "OK"}, "Sheaf.Paper.DiagonalCoefficientFiniteClosure": {"hash": "12ad9d3e52910d6228fc33c2f18bf43235ef3f1a", "status": "OK"}, "Sheaf.Paper.DiagonalCoefficientUniformizerReduction": {"hash": "02d6f4ae36b056979a3315ef3b66877f20a76568", "status": "OK"}, "Sheaf.Paper.DiagonalUniformizerScalarFrame": {"hash": "45fcc98a1c61fc1cea1ae8aff8854d1b1a9d31b9", "status": "OK"}, "Sheaf.Paper.RationalP1Triangle": {"hash": "d1e2d798a7453c8ae09756e0efc410fa7b065150", "status": "OK"}, "Sheaf.Paper.RationalP1UnitCounit": {"hash": "2a9dd0f68f8d2f9693022c3f44dd096a05940c3d", "status": "OK"}}, "seconds": 105, "time": "2026-10-28T03:04:49+0800", "transitive": 5, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

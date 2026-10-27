## What changed

Filled the canonical endpoint-normalization, projection-invertibility, section-arrow,
Tate-origin and exceptional-compositor proofs in `Sheaf.Paper.CoordinateSectionArrows`.
Existing declaration signatures are preserved. The unclaimed projection
and comparison modules use generic cached composition helpers for the same
canonical raw projection and inverse exceptional compositor;
see `coord/changes/C6-coordinate-projection-cached-composition.md` and
`coord/changes/C6-coordinate-compositor-cached-composition.md`. Private helpers
implement cancellation, Tate-power pullback, and the Hom-bijection argument for the
specified exceptional compositor.

## Proved and sorry left

All seven original holes are proved; the complete three-module sandbox compiles cleanly.
Holes closed: seven. Holes added: zero. Sorries left in delivered modules: zero.

Proved declarations:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.sectionProjection_isIso`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.oneTargetIso_existsUnique`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.sectionTargetIso_existsUnique`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.lastProduct_existsUnique`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.sectionArrow_existsUnique`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.target_origin`
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinateExceptionalComposition_isIso`

These declarations realize `def-pur-coordinate-section-arrows`. Holes added: zero.
No split-off statements or new nodes. The projection node also records proved
endpoint-composition and finite-Tor applicability helpers, plus a concrete projection-component cache, and the comparison node records the concrete
transpose helper. Both existing maps are unchanged after unfolding these helpers.

## No longer needed

Removed the unused private imports `Sheaf.Paper.PurTwistSheafLocallyFree`,
`Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`, and
`Mathlib.CategoryTheory.Adjunction.Mates`. The proof uses the existing fixed-ring
projection formula directly and proves invertibility of the specified compositor
from the existing Hom equivalences. No public imports, modules, declarations or
unit proof steps are withdrawn; these dependencies may remain needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

The item node has no numbered proof steps (`proof` and `proof_deps` were empty).
Its declaration docstrings supply the construction and proof plans. The Lean proof
uses the existing `target_properties` claim and canonical pullback to obtain finite
Tor constructibility on arbitrary bases, then the upstream fixed-ring projection
formula. No new mathematical statements with postponed proofs are needed.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

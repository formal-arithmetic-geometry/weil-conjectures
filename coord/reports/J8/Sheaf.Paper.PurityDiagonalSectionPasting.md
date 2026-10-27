## What changed

Partial proof delivery for `Sheaf.Paper.PurityDiagonalSectionPasting`.
Thirteen existing helper holes are filled. All existing signatures, definition
texts, declaration visibility and public imports are preserved.

The coefficient exponent is obtained from the existing finite comparison theorem.
The canonical tensor and base-change maps use the existing smooth duality results;
the latter uses the affine-locality extension without adding quasi-separatedness.
The two geometric squares are proved by their universal properties. Base-change
permanence gives the geometric dimensions and finiteness properties. Affine space
is treated by splitting and concatenating its coordinate tuples, including empty
blocks. Open restrictions use pullback projection equations and open-immersion
base change/cancellation. No arbitrary data is selected from an unproved existence.

Added proof import: `Sheaf.SixFunctors.SmoothDualityBaseChangeCompat`.
Local canonical monoidal instance priorities, irreducibility and pullback simp
attributes keep elaboration tractable. The context change is documented in
`coord/changes/J8-diagonal-pasting-local-proof-context.md`; no consumer is adapted.
The node's proof gains a helper-proof description and its actual dependencies;
the existing three-step plan for the unfinished final theorem is retained.
Source comparison confirms that all 46 existing definition/abbreviation blocks and
all public imports are textually unchanged. No new axiom or forbidden escape is used.
Server validation: lcompile.py compiled the complete module without errors or
warnings in 51.9 seconds (result 624c80bfce19fb818ed94ce9).

## Proved and sorry left

Closed 13 of the original 15 holes. Added 0 holes; split off 0 statements.

Proved `WeilConjectures.PurityFiniteSetting.comparedExponent` and these declarations
in `WeilConjectures.PurityFiniteSetting.DiagonalPasting`:

- `thetaIsIso`
- `betaIsIso`
- `geometry`
- `geometryProperties`
- `noetherianPullback`
- `affineGeometry`
- `affineDimension`
- `affineNoetherian`
- `openFactorProperties`
- `openPairProperties`
- `compositeSquare`
- `openMiddleProperties`

Exactly two existing named holes remain unchanged, both attached to
`lem-pur-diagonal-section-pasting`:

- `WeilConjectures.PurityFiniteSetting.DiagonalPasting.chartGeometry`
- `WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPasting`

This is helper-proof progress, not a proof of the final pasting theorem. The filled
smoothness helpers use existing library theorems and inherit their dependencies.

## No longer needed

Removed unused proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (already publicly imported by the
  retained `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`).

No DAG dependency module is claimed globally unnecessary. The final theorem remains
unfinished, so its original proof dependencies and unit route remain. No module or
node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The signatures used by the completed helpers are correct; zero dimensions, empty
coordinate blocks and empty schemes require no added assumptions.

Several declared dependencies of the final theorem currently import this module:
`DoubleDiagonalSectionIdentifications`, `AffineDifferenceTowerFactorization`, and
`DifferenceCoordinateSectionIdentifications`. Direct proof imports of these into
this file would create cycles. Their geometric statements are not treated as
withdrawn or unnecessary. This partial delivery proves the already separated
helpers without altering that unfinished assembly or introducing replacement holes.

The smooth base-change theorem in the synchronized upstream library requires
quasi-separatedness of the base. The existing `SmoothDualityBaseChangeCompat`
module supplies the earlier general signature by affine locality, so no hypothesis
repair was required here.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

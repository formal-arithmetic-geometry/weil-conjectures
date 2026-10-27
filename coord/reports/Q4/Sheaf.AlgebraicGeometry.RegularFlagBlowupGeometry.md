## What changed

Proved `AlgebraicGeometry.RegularFlagBlowupGeometry.regular_immersion_conormal_rank`
without changing its statement. Two proved private helpers transport the regular-sequence
basis of the affine cotangent module to conormal sections, then sheafify the resulting
coordinates. The inverse-image affine opens cover the source; the existing fixed-rank
local-to-global criterion gives the result, including codimension zero and empty sources.
This follows the standalone conormal assertion in Step 2 of the existing node; the full
flag theorem retains its original statement and nine-step proof plan.

## Proved and sorry left

Closed: `AlgebraicGeometry.RegularFlagBlowupGeometry.regular_immersion_conormal_rank`.

Left: `AlgebraicGeometry.RegularFlagBlowupGeometry.regular_flag_blowup_geometry`
(node `lem-per-regular-flag-blowup-geometry`), with its original nine-step proof plan.
The module originally had two holes; one is closed and one remains. No holes were added
or split off. The two private helpers are fully proved.

## No longer needed

Removed unused proof imports:

- `Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation`
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`
- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`
- `Sheaf.RingTheory.RegularSequenceGradedPolynomial`
- `WeilConjectures.Blowup.FiniteDegree.Algebra`

Added the proof import `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`.
All public imports are preserved. No nodes are withdrawn: the unproved full flag geometry
still needs its original plan.
The conormal-rank proof uses the existing affine-conormal identification, regular-sequence
basis theorem, and fixed-rank local-to-global criterion.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The algebraic basis and sheaf local-to-global APIs already exist;
no additional geometric theorem or new node is needed for the standalone conormal rank.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

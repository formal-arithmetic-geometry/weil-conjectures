## What changed

Replaced the item theorem's sorry with a proof constructing its restriction datum from
`affineLine_orientation`, cancelling the residue isomorphisms, and applying geometric
restriction injectivity. The new injectivity theorem is proved: it lifts degree-zero
maps to étale sheaf maps, uses geometric stalk conservativity, and applies the Gysin
evaluation bijection. A separate supported-stalk comparison remains unfinished.
No existing statement or definition was changed.

The resumed work also proves that normalized transports give identical derived
support restrictions: terminal-map uniqueness fixes the support unit after its monic
kernel inclusion. The supported-stalk statement now only asks for one compatible
transport at each geometric point. The injectivity proof transfers its formula to
the specified transport. File-level transparency settings avoid expensive unfolding
of the small-site functors; no definition or existing signature was changed.

## Proved and sorry left

Original holes: 1, in `affineLine_orientation_uniqueness`. Its proof now compiles with
no sorry. New `orientation_support_restriction_ext`, its private geometric-stalk
extensionality helper, and `orientationSupportRestriction_transport_eq` are proved
with no sorry. One new hole remains:
`affineLine_support_stalk`, node `lem-pur-affine-line-support-stalk`.
This is a decomposition: 1 original hole closed, 1 new hole added, net 0.

All three modules compiled together without warnings (4.8 s, 45.6 s, 17.3 s); the final injectivity module also compiled after
replacing the temporary geometric-point algebra compatibility hole by Spec.preimage.
The outstanding result is the comparison calculation, not a claim of stalk
conservativity for arbitrary pro-étale sheaves.

## No longer needed

The following direct proof-only imports were removed from the item module. Their
underlying results may still be needed in the proof of the outstanding comparison;
no transitive pruning is claimed:

- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`
- `Sheaf.Paper.PurityAffineLineDatum`
- `Sheaf.Paper.PurityGysinStructure`
- `Sheaf.Paper.ConcentratedComplexShift`
- `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.SupportedCohomologyHom`
- `Sheaf.AlgebraicGeometry.SupportLongExact`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.PurityRelativeKummer`

The item now directly uses only orientation existence and the new injectivity node.
The injectivity proof uses the supported-stalk comparison, étale comparison fullness,
geometric-point joint faithfulness and the Gysin evaluation bijection. No existing
module is withdrawn and no blueprint unit statement is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox packet isolated the entire injectivity assertion with a sorry.
That assertion is now proved from a separate pullback-and-stalk comparison. The
comparison itself is not proved, so the packet does not establish the original
statement without additional sorry dependencies. The earlier exit-137 dry-run failures
did not recur in the resumed attempt: the first
dry run reached the split-proof policy gate. Profiling then exposed expensive
definitional equality in the small-site functors. The transparency setting resolves
this without raising the compile limit. The remaining comparison is a separate
source calculation: existing supported-Hom naturality does not directly identify
the recorded Gysin chart with geometric stalk evaluation. It remains explicitly
unproved, rather than being inferred from conservativity alone.

## New nodes

`lem-pur-affine-line-orientation-injectivity`, module
`Sheaf.Paper.PurityAffineLineOrientationInjectivity`: proved geometric restriction
extensionality, using étale geometric stalks.

`lem-pur-affine-line-support-stalk`, module `Sheaf.Paper.PurityAffineLineSupportStalk`:
the remaining supported-Hom, pullback and geometric-stalk comparison from Step 4.
Its statement is uniform in the section being evaluated and supplies one compatible
transport and a fixed fibre identification; it does not assert global injectivity or normalized uniqueness.

The resumed preflight identified missing LeanSearch records on both new nodes.
The actual LeanSearch query was run and its results added alongside the retained
LeanFinder, Loogle and source-grep searches.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

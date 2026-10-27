## What changed

Restored `lean/Sheaf/Paper/RationalPurityPresentation.lean` from its current rework
archive. Restored normal transparency checking for elaboration instead of allowing
unfolding through protected derived and scalar constructions. Locally shielded
`ScalarLocalization.composition`, `ScalarLocalization.transportHom`,
`pbcRationalScalarHom`, `pbcPurityStageA` and `pbcPurityStageC` from the recursive
unfolding seen in the detailed profiler, particularly in transitivity and descent.
Locally prioritized the existing `Algebra.toModule` and
`ScalarLocalization.category` instances, avoiding the unrelated inference branches
recorded by the trace. All 39 declaration signatures, public imports, definition
bodies, exported attributes and exported instance priorities are preserved.

Proved `AlgebraicGeometry.Scheme.pbcPurityGeometricBounds` from the declared
finite-type Noetherian/dimension results and the prime-to-characteristic field unit
mapped to each stalk. Added the private proof import
`Mathlib.Algebra.CharP.CharAndCard`; there are no new declarations or assumptions.

Change record: `coord/changes/U4-rational-purity-presentation-elaboration.md`.

Validation: the final source compiled through `lcompile.py` in 37.3 seconds with
exit code 0 and no diagnostics, below the unchanged 60-second limit. The restored
archive initially compiled in 34.2 seconds; a transparency-only candidate compiled
in 33.5 seconds. Each run used a changing private dependency overlay, so these are
not controlled speedup measurements. The detailed trace exposed recursive
scalar-Hom reductions and unrelated instance-search branches; its large debug log
made that diagnostic run exceed the limit. All profiling/trace commands are removed
from the delivered source. No timeout limit is raised and no module is split.

## Proved and sorry left

Closed one of the archive's 13 holes:
`AlgebraicGeometry.Scheme.pbcPurityGeometricBounds`. Added zero holes and split off
zero statements. The assigned timeout repair is separate from that proof progress.

The following 12 existing public theorem holes remain, all attached to
`prop-pur-rational-purity-transitivity-summands` and retaining their original source
and complete natural-language proof docstrings:

- `AlgebraicGeometry.Scheme.pbcPurityModel_mem`.
- `AlgebraicGeometry.Scheme.pbcPurityOrdinaryTateModel_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityOrdinaryScalarModel_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityDerivedScalarModel_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityPull_mem`.
- `AlgebraicGeometry.Scheme.pbcPurityAmbientProperties`.
- `AlgebraicGeometry.Scheme.pbcPurityCoefficientChange_square`.
- `AlgebraicGeometry.Scheme.pbcPurityTwistedScalar_naturality`.
- `AlgebraicGeometry.Scheme.pbcPurityCompactScalar_properties`.
- `AlgebraicGeometry.Scheme.pbcPurityScalarNormalization_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityStageA_coherence`.
- `AlgebraicGeometry.Scheme.rationalPurityTransitivitySummands`.

There are no holes in definitions. The restored module has 12 holes in total.

## No longer needed

None. No module, import, dependency or DAG attachment is withdrawn. In particular,
zero live importers does not withdraw a quarantined module: the recorded parent and
unit proof route still need this item. The archive and its dependency graph stay.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined for a compile timeout;
its absence does not mean its mathematics was withdrawn. The current rework archive
already includes the earlier whiskerRight optimization to `PbcPurityDescent`, so
reapplying that same edit would be a no-op. This repair changes the remaining
file-wide transparency policy and adds local abstraction barriers for the actual
scalar-Hom constructions instead. The prior U4 return is only a historical
upstream-sync notice, not an instruction to delete this archive.

The geometric proof follows Step 1 and uses only its existing dependencies, so no
node proof route or attachment needs modification. The consumer scan finds no live
importers and one archived direct importer,
`Sheaf.SecSmoothPurity.RationalPurityTraceCoherence`; its interface is unchanged.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

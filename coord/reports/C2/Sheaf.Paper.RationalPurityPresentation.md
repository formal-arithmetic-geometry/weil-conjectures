## What changed

Worked from the current shared version of
`Sheaf.Paper.RationalPurityPresentation`, preserving U4's geometric-bounds proof
and local elaboration fixes. No declaration signature, public import or definition
body changes.

Proved lattice membership in the intrinsic coefficient presentation by the existing
bounded-predicate comparison and the stalkwise criterion for a global unit. Built
the ordinary Tate comparison from the identity-on-sections restriction composition
and identity restriction; sectionwise faithfulness proves uniqueness. Reused the
already proved, identically normalized ordinary scalar comparison. For the derived
scalar comparison, reused the stronger existing comparison and proved uniqueness
by canceling the counit on each complex and applying localization extensionality.
The normalized equation makes the counit invertible, avoiding any expansion of
the large derived-change-of-rings witness. Proved that
completed pullback preserves lattices by the uniform reduction criterion,
constructible reduction pullback, the strict constructibility criterion and the
strict pullback tower comparison.

Added proof imports of `PbcUniformReductionCriterion`,
`PbcConstructibleReductionPullback`, `PbcConstructibleReductionCriterion` and
`IsomorphismComparisonScalarExtension`. Updated Step 1 and Step 3 of the existing
node to record these arguments and their actual dependencies. All other numbered
steps remain, including the unfinished final assembly and the unit route.

Validation: the final source compiled through `lcompile.py` on the project server
in 32.1 seconds, exit code 0, with no diagnostics. All profiling and diagnostic
options were removed. Public imports, declaration names and file options agree
with the shared source. The added DAG dependencies have no path back to this node.

## Proved and sorry left

Closed five of the current module's twelve holes:

- `AlgebraicGeometry.Scheme.pbcPurityModel_mem`.
- `AlgebraicGeometry.Scheme.pbcPurityOrdinaryTateModel_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityOrdinaryScalarModel_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityDerivedScalarModel_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityPull_mem`.

Added zero holes and split off zero statements. These are complete Lean proofs
from existing named declarations, with no new assumptions. Some existing proof
dependencies remain project obligations, as intended by stage 3.

The seven remaining original theorem holes, each retaining its source and full
proof docstring and attached to
`prop-pur-rational-purity-transitivity-summands`, are:

- `AlgebraicGeometry.Scheme.pbcPurityAmbientProperties`.
- `AlgebraicGeometry.Scheme.pbcPurityCoefficientChange_square`.
- `AlgebraicGeometry.Scheme.pbcPurityTwistedScalar_naturality`.
- `AlgebraicGeometry.Scheme.pbcPurityCompactScalar_properties`.
- `AlgebraicGeometry.Scheme.pbcPurityScalarNormalization_existsUnique`.
- `AlgebraicGeometry.Scheme.pbcPurityStageA_coherence`.
- `AlgebraicGeometry.Scheme.rationalPurityTransitivitySummands`.

There are no holes in definitions. The module has seven holes in total. U4's
previously landed `pbcPurityGeometricBounds` proof is preserved and is not counted
among the five holes closed by this delivery.

## No longer needed

Removed these original proof imports, which the completed arguments do not use:

- `Sheaf.Paper.PbcIdempotentCompleteTriangulation`.
- `Sheaf.Paper.IntegralResidueTor`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.FiniteTorAmplitude`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.SfDerivedComplete`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`.
- `Sheaf.Paper.PbcRationalCategory`.
- `Sheaf.Paper.PbcRationalTransport`.
- `Sheaf.Paper.PbcScalarExtension`.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `Sheaf.Paper.IntrinsicQbarCategory`.
- `Sheaf.Paper.PbcFiniteStageKaroubian`.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational`.
- `Sheaf.Paper.RationalSmoothPurityCanonical`.

The strict pullback comparison is publicly available through the retained
coefficient imports, so no additional direct `PbcActualStrictPullback` import is
needed. Every public import remains verbatim. Some of the removed modules are
still reached through retained imports. No module is withdrawn, no upstream
declaration is removed, and no node or unit step is declared globally obsolete:
the remaining final proof still has its recorded dependencies.

## Where the brief, the DAG or earlier work was wrong

The initial item source was quarantined, with its archive and dependency route
preserved in the rework record. While this session was running, U4's timeout repair
and geometric-bounds proof landed and the shared source was restored. This packet
was rebased onto that restored source before proving the five additional holes.
The historical archive's thirteen holes are therefore not this delivery's baseline.

The two scalar-model comparison statements are already supplied by
`IsomorphismComparisonScalarExtension`: the ordinary statement is identical; the
derived statement there additionally fixes the completion comparison. The latter's
uniqueness for a conjunction alone does not prove uniqueness from only the counit,
so this delivery supplies a separate uniqueness argument: cancel the counit
on complexes and use localization extensionality.
No statement was weakened, and no definition repair or forced adaptation is needed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Proved `AlgebraicGeometry.Scheme.stratumReductionIso_exists` from the existing
ordinary augmentation-normalized comparison. The proof restricts to flat-term
K-flat representatives, where both reduction counits compute the derived functors.
Fully faithful restriction descends their comparison. Naturality along resolutions
extends its normalization, and cancellation after restriction proves uniqueness.
Private proved helpers provide K-flat preservation and the categorical descent glue.
All existing public signatures in the assigned module are unchanged.

Factored the body of `StratumReductionFormula` through the new public definition
`DerivedReductionComparisonFormula`. Unfolding it and the existing complex-functor
alias recovers exactly the previous representative equation. The abstract proof and
the concrete predicate now share that definition. Profiling isolated a 50–65 second
kernel conversion; with the shared predicate it takes about 1.2 seconds. The new
module contains only this definition, with no theorem proof moved out of the item.
The change record `coord/changes/Q1-stratum-representative-formula.md` records the
old/new bodies and the consumer review. All other existing public definitions and
all public signatures are unchanged. No adopted-source module changes.

Added proof imports of ReductionPullbackDerivedTower and AdicCoefficientDatum
(including their private descent helpers), ProEtaleAlgebraicInverseImage,
ProEtaleToposFunctorialityInverseImage, and KFlatRingedToposPullback.
Updated the existing DAG proof to describe the representative descent and its
additional dependencies. The blueprint unit route stays intact.

Validation: `lcompile.py --all` passes cleanly for the two delivered modules
(2.3 s and 43.0 s). A temporary probe reproduced the previous formula verbatim and
proved its equivalence to the new one by `Iff.rfl` (30.0 s). The probe is not delivered.

## Proved and sorry left

Closed one of the six original holes:

- `AlgebraicGeometry.Scheme.stratumReductionIso_exists`.

Added zero holes and split off zero statements. The new definition module has zero holes.
The five remaining holes are unchanged named theorems, all attached to
`lem-weil-pbc-stratum-completion-unit-restriction`:

- `AlgebraicGeometry.Scheme.stratumModuleReductionIso_exists`.
- `AlgebraicGeometry.Scheme.stratumReduction_normalization`.
- `AlgebraicGeometry.Scheme.stratumReduction_evaluation`.
- `AlgebraicGeometry.Scheme.stratumReduction_augmentation`.
- `AlgebraicGeometry.Scheme.stratumRlimComparison_isIso`.

The previously proved finite-coefficient naturality, restriction limits, completion-unit
comparison, intrinsic preservation, and finite-stratum detection proofs are retained.
No definition chooses an arbitrary witness of mere existence.

## No longer needed

None. No original imports, declarations, modules, or DAG dependencies are removed.
The remaining ordinary, normalization, evaluation, augmentation and inverse-limit
obligations still require their recorded dependencies. No blueprint unit statement
or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The anonymous concrete representative equation caused
costly kernel conversions when compared with an abstract copy of that same equation.
The shared public predicate avoids those conversions while preserving the exact
normalization. The derived comparison needs no new split:
resolving-representative descent supplies the argument from the existing ordinary
comparison. Extending normalization along a resolution uses invertibility only in
the source derived functor; no preservation of K-flatness under arbitrary
quasi-isomorphisms is assumed.

The unchanged consumer `CompletedDirectImageLimits` finishes checking without Lean
errors but exceeds the local compile limit: 91.1 s against this packet, and 97.8 s
against the original library with the delivered item absent from local overrides.
The baseline profile includes 53.9 s of linting and 35.7 s of attribute application
(overlapping timings). This existing timing issue is reported for maintenance;
that consumer is not edited or included in the delivery.

## New nodes

`def-weil-pbc-derived-reduction-comparison-formula` attaches the new shared predicate
in `Sheaf.Paper.DerivedReductionComparisonFormula`. It names the equation already
required by the item, without asserting it, choosing data, or adding a hypothesis.
The actual categorical descent proof stays in the assigned module. The change record
is `coord/changes/Q1-stratum-representative-formula.md`.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

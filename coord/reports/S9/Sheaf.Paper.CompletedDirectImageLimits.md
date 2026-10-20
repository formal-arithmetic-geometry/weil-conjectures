## What changed

Proved `AlgebraicGeometry.Scheme.completedOrdinaryReductionPullbackInv_isIso`
in `Sheaf.Paper.CompletedDirectImageLimits`.

The proof takes a second mate across the module pullback/direct-image adjunctions.
That mate is the existing scalar-restriction/direct-image isomorphism. The
iterated-mate/conjugate identity and invertibility of conjugates finish the proof.
This avoids constructing another tensor-balancing comparison.

Updated the existing node's proof, proof dependencies and proof origin to record
this shorter argument. Public signatures, definitions and public imports are unchanged.
No new proof import is required.

## Proved and sorry left

Closed 1 of the 6 original holes:

- `AlgebraicGeometry.Scheme.completedOrdinaryReductionPullbackInv_isIso`.

No holes added; no statements split off. Five original holes remain unchanged,
all attached to `prop-weil-pbc-direct-image-limits`:

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerPushEvaluation_existsUnique`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlim_roos`.
- `AlgebraicGeometry.Scheme.completedReductionLevelPullbackIso_transition`.
- `AlgebraicGeometry.Scheme.completedReductionPullbackIso_existsUnique`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerProjection_properties`.

An evaluation proof candidate using uniqueness of right-derived pairs compiled
without warnings in 29.8 seconds, but exceeded the 60-second limit with the axiom
probe. It is excluded from this packet; its original theorem remains a whole named
sorry. In diagnostic compiles, the retained scalar proof passed the full probe in
16.3 seconds. The required delivery dry run checks the final packet again.

## No longer needed

Removed the following unused private proof imports:

- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.CompletedDerivedInverseLimit`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`.
- `Sheaf.Paper.KoszulReconstruction`.
- `Sheaf.Paper.PerfectProjectionFormula`.
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.Algebra.Homology.RoosComplex`.

These imports are unnecessary for the current Lean proofs. No entire DAG node or
module is withdrawn: the remaining theorem clauses retain their mathematical
proof plans. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The ordinary scalar comparison
has a shorter categorical proof than the proposed local pure-tensor calculation:
its double mate is already an isomorphism.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

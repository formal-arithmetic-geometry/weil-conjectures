## What changed

Proved seven existing theorems of `Sheaf.Paper.CompletedSupportIntermediateTower`.
All existing signatures, definitions, attributes, public imports and docstrings are unchanged.
No source-library module is changed. Added the proved private helper
`finiteComparison_isIso`, identifying the finite proper mate with the existing
`AdicCoefficientDatum.finiteProjection`; its existing invertibility theorem supplies the
proper factor. Moved `finiteAndIntrinsic`, with its unchanged signature and docstring,
after `retainedOrigins` so it can use the explicitly constructed normalized witness.
The retained witness uses exactly the stated bounded-below antecedent and the inverse
of the actual finite comparison, rather than an unrelated existence witness.

The ringed reduced-unit proof uses homology and exact evaluation to detect invertibility
of the strict diagram map. It makes no assertion that evaluation is faithful on maps.
The coefficient open mate uses the existing equivalence of scalar restriction along a
coefficient isomorphism. Private imports with `import all` expose the existing proved
scalar-unit, scalar-equivalence and inverse-mate helpers used by these proofs.

The DAG gains an implementation step and the existing four-arrow, pro-etale operation and finite transport
prerequisites used by this proof. Its original mathematical argument remains for the
remaining helper obligations. No new node or theorem with `sorry` is introduced.

## Proved and sorry left

Original holes: 16. Closed: 7. Added: 0. Remaining: 9.
All names below are in `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower`
and attached to node `lem-cbc-completed-support-intermediate-tower`.

Closed:

- `finiteScalarSquare`
- `finiteScalarOpenInverse_isIso`
- `originScalarUnit`
- `retainedOrigins`
- `finiteAndIntrinsic`
- `ringReducedUnit`
- `completedSupportIntermediateTower`

Also proved the private helper `finiteComparison_isIso` without a new hole.

Remaining, with their original source and proof docstrings:

- `strictUnits`
- `completionUnits`
- `reconstructionNormalization`
- `ordinaryOpenInverse_isIso`
- `endpointInsertions`
- `exchangeSubstitution`
- `finiteUnits`
- `twoSubstitutions`
- `strictFiniteCoherence`

This is a partial delivery for the module. Its main assertion is now assembled from
the existing named intermediate assertions. The remaining assertions are unchanged;
the proof still depends on their existing postponed proofs.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.Paper.StrictQuotientScalarBalancing`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.ConstantPerfectQuotientProjection`
- `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.Algebra.Homology.LocalizedStrictTensorDescent`
- `Sheaf.Paper.RingedExchangeTensorCoherence`

These imported proof plans are not used directly by the seven proofs delivered here.
No module or DAG node is withdrawn: remaining postponed helper proofs retain their
mathematical dependencies, and public imports still reach some of these modules.
The unit route stays intact. No claim of whole-closure module pruning is made.

## Where the brief, the DAG or earlier work was wrong

The finite projection is already available with exactly its mate normalization in
`AdicCoefficientDatum.finiteProjection_isIso`; no fresh projection formula is needed.
The apparent need to prove `finiteAndIntrinsic` before constructing normalized origins
is avoidable: prove finite comparison invertibility separately, construct the normalized
origin, and assemble completeness and existence afterward. No statement repair is needed.
The latest blueprint now presents the condensed compact-support argument, whereas this
existing node records the reviewed completed strict-tower interface. This delivery
preserves that interface and does not replace the unit's statement or route.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

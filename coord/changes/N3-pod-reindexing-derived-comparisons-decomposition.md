## Reason

The assigned proof is a conjunction of five derived comparison laws and a separate pullback normalization. The definitions are moved to a public support module so the two named split obligations can share one witness.

## Old

`Sheaf.Paper.PodReindexingDerivedComparisons` defined the data and all laws in one module and left the existential theorem as one proof obligation.

## New

`Sheaf.Paper.PodReindexingDerivedComparisonsCore` owns and publicly exports the unchanged data definitions and supplies the five-law core theorem. `Sheaf.Paper.PodReindexingDerivedComparisonsPullback` proves, from `primitiveQuotientPullbackModelExistence`, that the `pullback` field of any witness can be replaced by a normalized realization. (Reviewer FIX: the delivered version asserted the normalization for every witness, which is false, since the normalized realization is unique.) The five core laws do not read that field. The assigned module reexports the support module and assembles the original flat `Laws` conjunction.

## Users

- Sheaf.Paper.CompactSupportProjectionFormula
- Sheaf.Paper.FiniteRestrictionDiagramNaturality
- Sheaf.Paper.PodNormalizedTensorSignedShifts
- Sheaf.Paper.PodReindexingCompletedEvaluationReflection
- Sheaf.Paper.PodReindexingCompletionUnitTensor
- Sheaf.Paper.PodReindexingHomCoefficientDescent
- Sheaf.Paper.SfPackageExceptionalCoherenceRealization
- Sheaf.Paper.SfPackageLocalizationProjectionRealization
- Sheaf.Paper.WeilChosenDualityExchange
- Sheaf.Paper.WeilChosenDualityExchangeData

## Status

landed 20261027T234120-L-2334 2026-10-27 (merge of deliver/N3/Sheaf.Paper.PodReindexingDerivedComparisons)

# AlgebraicGeometry.Scheme.adicDatumRing

## Reason

The completed ring is still exactly adicLisseCompletedRing T d.ideal, the actual inverse limit of the quotient ring sheaves. Change its abbreviation to a definition so this module can locally keep the chosen limit cone irreducible. The proved adicDatumProjection_comp exposes its naturality equation. This prevents accidental expansion of the chosen cone in scalar, tower and tensor types; downstream it is an ordinary semireducible definition with the identical body.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

The unclaimed consumer `Sheaf.Paper.CompletedFiniteReductionTensorComparison`
needs an explicit category argument `(C := B)` at its tensor-left/right comparison.
After normalizing its scalar-functor proof aliases, inference reported
`failed to synthesize MonoidalCategory (SheafOfModules (...adicLisseCompletedRing...))`
at original line 143: the residue's expanded coefficient presentation no longer
selects the local instance at the named completed-module category automatically.
Supplying that same category uses the existing local monoidal and symmetric instances.
Only this proof application changes; all public signatures remain identical.

## Old

```lean
abbrev adicDatumRing := adicLisseCompletedRing T d.ideal
```

## New

```lean
def adicDatumRing := adicLisseCompletedRing T d.ideal
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.CompletedFiniteReductionTensorComparison | unclaimed | Supply the completed-module category explicitly in the private proof computation. |
| Sheaf.Paper.CompletedFiniteReductionTensorModel | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteLevelRectangle | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteProjectiveTensorProducts | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.SequentialDerivedInverseLimitCompleted | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)

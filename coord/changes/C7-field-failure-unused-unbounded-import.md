# FieldFailureOfCumulativeBaseChange public import pruning

## Reason

The statement and proof use the bounded-below degreewise base-change property and existing
field-detection theorem. The unbounded derived exchange module is unnecessary. Remove its
public import as well as the unused proof imports. No theorem signature, definition or
visibility changes. The two replacement proof imports remain private to the module.

## Old

```lean
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
```

## New

The public import above is removed. The public imports of
`Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty` and
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.FieldFailure`
are unchanged. The existing theorem signature is unchanged, and its proof now uses private
imports of `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection`
and `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FieldFailureOfCumulativeBaseChange
--uses exists_fieldFailure_of_cumulativeUniversalBaseChangeProperty` found these two
transitive consumers. The current source of both contains no application of the theorem
(their proof plans name it, but their proofs are still open). Both are compiled unchanged
against the sandbox output. No consumer adaptation is necessary; their statements and target
meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum | X2 | Unchanged; directly imports DerivedUnbounded itself. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | P3 | Unchanged; imports the previous consumer, which retains its public DerivedUnbounded import. |

## Status

landed 20261018T062718-L-638050 2026-10-18 (merge of deliver/C7/Sheaf.AlgebraicGeometry.FieldFailureOfCumulativeBaseChange)

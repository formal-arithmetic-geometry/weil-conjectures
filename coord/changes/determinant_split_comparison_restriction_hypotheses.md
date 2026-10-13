# determinant_split_comparison_restriction_hypotheses

## Reason

The corrected restriction theorem is proved solely by substituting `hd` into `hn`.
Neither the rank equality nor the finite-locally-free instances occur in that proof.
They are removed as part of the queued repair of the formerly false unconstrained-`c`
statement.

## Old

The corrected theorem still accepted `(r₂ = r₁ + r₃)` and the two
`IsFiniteLocallyFreeOfRank` instances before `V`.

## New

The theorem accepts only `(S) (r₁ r₂ r₃)` before `V`; its natural-family hypotheses
and conclusion are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | forced proof adaptation: remove the explicit `hr` argument at the theorem call; its public signature is unchanged |

## Status

landed 20261013T201806-L-3975987 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)

## Forced adaptations

`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison` previously failed against
the changed theorem interface because its call supplied `hr` where the next argument is
now `V`. The delivered caller removes exactly that argument and compiles with all other
lines unchanged.

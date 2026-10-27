# Strict quotient coefficient constructions extracted

## Reason

The unchanged direct consumer `QuotientExpressionStrictKFlatTowers` failed its
compile with `NOT ACCEPTED: this compile took 76 s > 60 s`. A profiled run passed
at 55.7 seconds, but the next plain run failed at 75 seconds. Local instance
priority adjustments did not improve the limit. Split the already complete
coefficient and transition constructions from the remaining strict tower proof.
Every public declaration keeps its original name, signature and body verbatim.
No statement or mathematical definition changes. No hole is added.

## Old

`Sheaf.Paper.QuotientExpressionStrictKFlatTowers` defined the expression syntax,
its interpretation, the coefficient pullback and reduction comparisons,
`SystemGood`, and the constant-map and unit-transition theorems before its
remaining K-flat tower proofs. Its original eight public imports are retained.
Its proof-only `import all Sheaf.Paper.AmbientPullbackTensorCoherence` was used
only for the already-proved normalized bundle existence construction.

Public imports, verbatim:

```lean
public import Sheaf.Paper.StrictQuotientExpressions
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.NormalizedDVRTower
```

## New

`Sheaf.Paper.QuotientExpressionCoefficientData` contains those original
constructions and the constant-map and unit-transition proofs, verbatim.
The existing module adds `public import Sheaf.Paper.QuotientExpressionCoefficientData`
and retains the remaining original proofs and definitions verbatim. The new
module retains the original eight public imports. Selected proof-only imports
move with the code using them. The existing module now privately imports
`Sheaf.Paper.AmbientPullbackTensorData` for `tensorData_existsUnique`, avoiding an
unused dependency on the final ambient coherence theorem.

The existing expression-data, constant-map and unit-transition DAG nodes retain
their statements and proof records and move only their Lean module/file attachment.
The original final node keeps its final theorem attachment; seven canonical
coefficient constructions move to the new node
`def-sf-strict-quotient-coefficient-comparisons`. The tower-data node cites the
normalized bundle construction actually used, instead of ambient coherence.
The strict quotient unit route is preserved.

Public imports, verbatim:

```lean
public import Sheaf.Paper.StrictQuotientExpressions
public import Sheaf.Paper.QuotientExpressionCoefficientData
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.NormalizedDVRTower
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientExpressionStrictKFlatTowers | unclaimed | Same public API and definition bodies by reexport. |
| Sheaf.Paper.QuotientExpressionCoefficientData | G2, new | Existing coefficient constructions and two proofs relocated. |
| Sheaf.Paper.QuotientExpressionKFlatModels | unclaimed | Unchanged source compiled against the delivered reexport. |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | unclaimed | Unchanged source compiled against the delivered reexport. |

Both direct importers compile successfully against the new location. Their
unchanged check copies are not part of the delivery. No source-library file changes.

## Status

landed 20261027T205959-L-1641374 2026-10-27 (merge of deliver/G2/Sheaf.Paper.AmbientPullbackTensorCoherence)

# fg_commutative_monoid_finite_presentation

## Reason

Repair the return at head `5a40dd576b1`: the source ledger read the dotted
warning option name as an unattributed proof-hole marker at line 30, offset 987.
The retained theorem proof is complete. Remove the unnecessary warning option,
so compilation reports any actual proof hole normally. Preflight requires this
record because the file-level command context changes.

## Old

```lean
set_option warn.sorry false
```

The theorem signature is unchanged.

## New

The warning-suppression command is removed; Lean uses its normal warning policy.
No definition, statement, exported attribute or public import changes. The
private proof imports and the complete theorem proof are those described in
report.md. The DAG records the direct finite-binomial-ideal proof.

## Users

The source-only downstream check lists 30 downstream modules. Its `--uses`
check finds the theorem name only in its own declaration, since downstream
proofs may still be unfinished. The unchanged theorem interface preserves their
planned uses. The warning option affects elaboration in this file only, so no
consumer adaptation or target statement review is required.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation` | A7 | Remove unused warning option; complete proof, unchanged signature. |
| `Sheaf.AlgebraicGeometry.ChartLogSmoothDeformationCalculus` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FSLogInfinitesimalCriterion` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.KatoLatticeChartRealization` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogBlowupNormalization` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogRegularCompletedChart` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogRegularMonomialTensor` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogRegularSharpChart` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogSmoothLogRegular` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.LogSmoothPreservesLogRegularity` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.DeligneLaumon.TraitLogSmoothUniformizerChart` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.RingTheory.CompleteToricFacetValuations` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.RingTheory.CompleteToricModel` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.SixFunctors.TraceFormula.NodalLogRegularity` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.CompleteToricKatoRecognition` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.CompleteToricMonomialFactors` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.KatoTorIndependenceChart` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.LogChartFaceTorComparison` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.LogRegularDesingularization` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.LogRegularDivisorialStructure` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |
| `Sheaf.TraceFormula.LogRegularToricRefinement` | unclaimed | Unchanged declarations, definitions and imports; no adaptation needed. |

## Status

landed 20261023T120532-L-629852 2026-10-23 (merge of deliver/A7/Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation)

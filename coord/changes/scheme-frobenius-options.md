# Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial module options

## Reason

The returned delivery was rejected because the landing audit attributed the file-level
`set_option warn.sorry false` token as an anonymous hole. The repair removes that
option, along with development-only `profiler` and unscoped `maxHeartbeats` options
that were present only in the retained debugging packet. The proof theorem and all
public declarations keep their existing signatures and meanings. This record covers the option commands flagged as an interface change by the
static preflight. No declaration, notation or instance exported to importers changes.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

The interrupted debugging copies additionally used:

```lean
set_option profiler true
set_option maxHeartbeats 20000
```

## New

```lean
set_option autoImplicit false
```

The theorem proof is compiled with the project's normal compiler options.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | observes the module interface; no declaration or signature change |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.ArithmeticRoots | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.DlConstantFieldCharts | G8 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.IteratedWeilCocycle | D4 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.IteratedWeilMap | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.RationalStalkExact | A7 | observes the module interface; no declaration or signature change |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.WeilOne | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | M2 | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | observes the module interface; no declaration or signature change |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 | observes the module interface; no declaration or signature change |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | observes the module interface; no declaration or signature change |
| TargetsCheck | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.Statement | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.Examples | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | observes the module interface; no declaration or signature change |
| WeilConjectures.ZetaFunction.Weights | unclaimed | observes the module interface; no declaration or signature change |

## Status

landed 20261020T131214-L-1259767 2026-10-20 (merge of deliver/V7/Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial)

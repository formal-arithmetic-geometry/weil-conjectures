# native_weil_tensor_ringed_chain_data

## Reason
The old theorem quantified over an arbitrary endomorphism assignment `sign`. Such an assignment can send a nonzero summand to zero, so the claimed isomorphism and summand equation are false. The corrected interface requires the normalized Koszul scalar action.

## Old
theorem native_weil_tensor_ringed_chain_data (U : NativeWeilRingedTensorUnderivedData b T adj) (sign : ∀ (_p _q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R} (_f : Y ⟶ Z), Y ⟶ Z) : Nonempty (NativeWeilRingedTensorChainData b T adj U sign)

## New
theorem native_weil_tensor_ringed_chain_data (U : NativeWeilRingedTensorUnderivedData b T adj) (sign : ∀ (_p _q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R} (_f : Y ⟶ Z), Y ⟶ Z) (hsign : ∀ (_p _q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R} (_f : Y ⟶ Z), sign _p _q _f = letI : AddCommGroup (Y ⟶ Z) := @Preadditive.homGroup (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) _ inferInstance Y Z ZSMul.zsmul ((_p * _q).negOnePow : ℤ) _f) : Nonempty (NativeWeilRingedTensorChainData b T adj U sign)

## Users
| module | group holding it | effect |
|---|---|---|
| `Sheaf.Algebra.Homology.KFlatBifunctorTensorHom` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.DeligneLaumon.GeometricCurveDiagramDescent` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.DeligneLaumon.MarkedGeometricCurveModel` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.DeligneLaumon.PairEigenvalueCurveTest` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.DeligneLaumon.SmoothAffineConstituentPurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.DerivedWeilOperations` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.DerivedWeilTensorOperations` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeCompactProjectionFormula` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeDerivedWeilTensorConstructible` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeGeometricHomComparison` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeGeometricTensorComparison` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenDerivedTensor` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenSheafProjectionTensor` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenSheafTensorExistence` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorComparisonData` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorComparisons` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorForgetNormalization` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorLocalization` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorNormalization` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorOperations` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorPresentationExistence` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeOpenTensorUnitNormalization` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilClosedForgetful` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilDualizingHomTransposition` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilRingedTensorModel` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorAdjoints` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorCoherence` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorConstraintLifts` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorGeometry` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorLift` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedComplexModel` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedComplexes` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquare` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedModel` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedModelNaturality` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedTransport` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorTransport` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilUnitMateIsIso` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.WeilCompactStructureTensorComparison` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.WeilGeometricHomConstructibility` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.WeilSheaf.OrdinaryClosedPresentation` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.WeilSheaf.StructuralBidualInvertible` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `TargetsCheck` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.Statement` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.Karoubian` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.KaroubianPointer` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedChainData (1)` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedComplexes (1)` | unclaimed / downstream | recompiles against corrected sign hypothesis |
| `Sheaf.Paper.NativeWeilTensorRingedComplexes` | W8 | forced adaptation: supplies the normalization proof for `nativeRingedTensorSign` |

## Status
landed 20261027T233915-L-4134784 2026-10-27 (merge of deliver/E5/Sheaf.Paper.NativeWeilTensorRingedChainData)

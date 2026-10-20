# Completed projection route interface split

## Reason

The existing public data declarations are placed in a dedicated data module so the independent proof modules can import them without an import cycle. Public names, signatures, and bodies are unchanged; the original theorem module publicly imports the data module.

## Old

The corner, tensor, completion, finite tensor, and coherence data declarations were in `lean/Sheaf/Paper/CompletedProjectionCoherence.lean` together with the proof.

## New

The declarations are in `lean/Sheaf/Paper/CompletedProjectionData.lean`, and `CompletedProjectionCoherence` publicly imports it. The proof imports the three independent split-result modules.

## Users

| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.CompositionProjectionMate | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.GeneratorReductionStatement | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.IntegralSystemOperations | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unchanged | public declarations and signatures unchanged |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unchanged | public declarations and signatures unchanged |
| Sheaf.Targets.AffineSpaceRationalLine | unchanged | public declarations and signatures unchanged |
| WeilConjectures | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.RationalSmoothPurityCanonical | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SixFunctorDatum | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SixFunctorOperationDatumStages | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SmoothPurityTowerClasses | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SystemClopenTensorCompatibility | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.TensorAdjunctionExchange | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.TowerClassChern | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.TowerClassProjective | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.TowerClassTwisting | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.VerdierExchange | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.WfTensorCompletionFrobenius | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.DiagonalTowerTracePresentations | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.EtaleRhoMonoidalMate | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.FiniteAdicImageNormalization | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.FiniteFreeCompactComposition | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.PointIdentityAdmissibility | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.PurityCoprojection | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.QcqsCompactSupportRealization | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.RationalDirectImageRealization | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.AdicSectionCanonicalModels | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.AdmissibleVerdierExchange | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.BoundaryDualizingComposition | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.CoefTowerCoaugmentation | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.CompactSupportProjectionFormula | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.ConnectedConstantH0 | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.CoprojectionCompositionMate | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.DiagonalTowerTraceModels | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unchanged | public declarations and signatures unchanged |
| Sheaf.Paper.GlobalVerdierDuality | unchanged | public declarations and signatures unchanged |

## Status

landed 20261020T221357-L-4179895 2026-10-20 (merge of deliver/V1/Sheaf.Paper.CompletedProjectionCoherence)

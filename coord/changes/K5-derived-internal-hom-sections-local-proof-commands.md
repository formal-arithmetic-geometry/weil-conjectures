# DerivedInternalHomSectionsModel local proof commands

## Reason

Preflight conservatively classifies the newly added scoped `open`, `omit` and local
`attribute` commands as a change to what importers see. This record documents the commands;
all existing public signatures, data definitions, instances, attributes and public imports
remain unchanged. Only the assigned theorem proof, new proved private helpers and private
proof imports change. No target meaning changes and no consumer requires adaptation.

## Old

Immediately after the namespace opening, the original file has:

```lean
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
```

There are no `sectionsComparison`, `externalDerivedEquiv`, `precompHomologyData`,
`externalMap_quasiIso`, `bijective_precomp_quotient` or `globalMap_quasiIso` private helpers,
and no local irreducibility commands for the constants listed below. The assigned
`derived_internalHom_sections_model` proof is `by sorry`. The already proved
`tensorRightAdjoint_iso` body is preserved verbatim.

## New

The variable commands and every existing declaration signature remain verbatim. The new
private helpers precede those variables, or are scoped to them as required. Their local
elaboration commands are:

```lean
open CochainComplex HomComplex Preadditive in
open CochainComplex HomComplex in
attribute [local irreducible] sectionsComparison Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit
attribute [local irreducible] homComplexFunctor CategoryTheory.globalComplexIso
omit [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}] in
```

Each `open ... in` and `omit ... in` applies to its immediately following private declaration.
The irreducibility attributes apply only inside this file and prevent expensive unfolding
of functor and complex constructions. Scoped `backward.isDefEq.respectTransparency false`
options apply to the private proofs and the completed theorem; scoped `maxHeartbeats 300000`
applies to that theorem. No new global option, instance, attribute or notation is exported.
Every helper is fully proved. The main theorem now proves the four original clauses.

## Users

The table contains the item and all transitive source importers from
`python3 tools/downstream.py Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel --names`.
The companion `--uses derived_internalHom_sections_model tensorRightAdjoint_iso` query finds
only the item itself and `Sheaf.Algebra.Homology.RhomHypercohomologyBridgeOfUniverses`.
Claims are read from the current project records. No downstream module is edited or needs
adaptation, because the changes are private and local and public signatures are identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | K5 | New private proof helpers and local commands; signatures unchanged. |
| Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedCoinductionAdjunction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor | unclaimed | No exported change; no adaptation required. |
| Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses | unclaimed | No exported change; no adaptation required. |
| Sheaf.Algebra.Homology.RhomHypercohomologyBridgeOfUniverses | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | U1 | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | No exported change; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | C8 | No exported change; no adaptation required. |
| Sheaf.Paper.AdicCohomologyTorsionNormalForm | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | K4 | No exported change; no adaptation required. |
| Sheaf.Paper.AdicTorFlatCohomology | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.AdicTorFlatCriterion | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | U8 | No exported change; no adaptation required. |
| Sheaf.Paper.CoefficientExtensionReductionModel | Y2 | No exported change; no adaptation required. |
| Sheaf.Paper.CoefficientHomZeroClass | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.CoefficientRingedSequenceSite | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.DeltaProperPushforward | S7 | No exported change; no adaptation required. |
| Sheaf.Paper.ExternalRHomConePairing | J7 | No exported change; no adaptation required. |
| Sheaf.Paper.FinitePerfectAdicRealization | W3 | No exported change; no adaptation required. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.IntegralHomAugmentedTowerComparison | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.IntegralHomModelsExist | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.IntegralHomReduction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.IntegralHomReductionTowerComponents | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.IntegralHomRoosTransport | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.LevelwiseAdicTruncations | K2 | No exported change; no adaptation required. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PbcConstructibleReductionCriterion | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PbcUniformLocalModelCohomology | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PbcUniformReductionCriterion | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PointDerivedHomEvaluation | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PointDerivedHomModels | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PointExtensionKFlat | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PointHomComplexAdjunction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PointSheafHomMaps | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PointTensorHomEvaluation | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.ResidueLissePerfectLift | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientAssociatorShifts | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientProjectionData | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientPullbackCoherence | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientPullbackComparison | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientPullbackShifts | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientScalarShifts | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedCoefficientScalarUnits | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedRefinementData | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearDerivedCalculus | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearDerivedSections | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearGeometryCore | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearGeometryDerived | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearGeometryOps | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearOperationsExistence | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearSystemModels | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SemilinearSystemsExistence | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SystemCochainTensorReduction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SystemEvaluationFlat | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SystemNormalizedTensorClosure | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SystemOrdinaryTensorReduction | unclaimed | No exported change; no adaptation required. |
| Sheaf.Paper.SystemTensorMateArrows | R3 | No exported change; no adaptation required. |
| Sheaf.Paper.SystemTensorReductionFormula | unclaimed | No exported change; no adaptation required. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | No exported change; no adaptation required. |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | C6 | No exported change; no adaptation required. |
| Sheaf.SixFunctors.ClosedCostalkDuality | V4 | No exported change; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | unclaimed | No exported change; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates | unclaimed | No exported change; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData | unclaimed | No exported change; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom | unclaimed | No exported change; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor | unclaimed | No exported change; no adaptation required. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | V2 | No exported change; no adaptation required. |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | unclaimed | No exported change; no adaptation required. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed | No exported change; no adaptation required. |
| Sheaf.TraceFormula.DerivedBasisLocalExtSheaf | unclaimed | No exported change; no adaptation required. |
| Sheaf.TraceFormula.PolynomialDiagonalRhomReduction | unclaimed | No exported change; no adaptation required. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed | No exported change; no adaptation required. |

## Status

landed 20261021T003508-L-1643733 2026-10-21 (merge of deliver/K5/Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel)

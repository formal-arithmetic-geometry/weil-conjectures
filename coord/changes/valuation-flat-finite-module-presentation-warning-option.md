# Algebra.valuation_flat_finite_module_presentation

## Reason

Repair the returned landing failure at `<unattributed:36:1236>`. The source hole scanner
recognizes the component `sorry` of the option name `warn.sorry` as an unattributed hole.
The completed theorem contains no hole and needs no warning suppression, so remove the
obsolete option. The delivery preflight treats a change to this module-level command as
an interface change and requires this record. The mathematical statement, definitions,
public imports, universes and instances are unchanged. No target needs statement review.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

The declaration `Algebra.valuation_flat_finite_module_presentation` keeps its existing
signature verbatim; its proof is completed by finite type descent and localization.
The removed command controls only warning emission in this file. It introduces no
mathematical declaration and affects no consumer's elaborated statement or definition.

## Users

The table includes every transitive downstream module listed by
`python3 tools/downstream.py Sheaf.TraceFormula.ValuationFlatFiniteModulePresentation
--uses Algebra.valuation_flat_finite_module_presentation`, together with the item.
The only direct importer is `Sheaf.TraceFormula.ValuationFiniteModuleInjectivity`.
No consumer currently references the theorem in a proof; the parent still has an
unfinished proof. Its import and DAG dependency are preserved. No consumer file is adapted.
Holder names reflect the current local claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.TraceFormula.ValuationFlatFiniteModulePresentation | E6 | Item proof completed; unused warning suppression removed; signature unchanged. |
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericFreeBlowup | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HighGenusHomClosure | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalCurveLCICriterion | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalCurveStackSmooth | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NodalTraitRegularization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.PersistentNodeNormalization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry | A5 | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.BaseModificationComparisonFibreImage | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FlatAssociatedEquidimensional | X6 | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FlatFibreComponentClosureDimension | Q7 | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FlatFibreFreeNeighbourhood | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | E4 | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | P8 | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.NoIsolatedContractedFibreComponent | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.NodalFamilyNoetherianApproximation | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationFiniteModuleInjectivity | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | No type or definition change; no adaptation required. |
| Sheaf.TraceFormula.ValuativeDominationEtaNormal | unclaimed | No type or definition change; no adaptation required. |

## Status

landed 20261023T123456-L-1195139 2026-10-23 (merge of deliver/E6/Sheaf.TraceFormula.ValuationFlatFiniteModulePresentation)

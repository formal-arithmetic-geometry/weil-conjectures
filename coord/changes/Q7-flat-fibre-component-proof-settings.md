# AlgebraicGeometry.flat_fibre_component_closure_dimension

## Reason

The complete proof adds private stalk and topological helpers. Preflight classifies the
additional `open` and elaborator-option commands as an interface change and requests this
record. These commands only affect elaboration within this file. No public signature,
instance, attribute, definition, notation or public import changes; no consumer adaptation
is necessary. All private definitions are explicit constructions with complete proofs.

The repair retains the original private import
`Sheaf.TraceFormula.FlatAssociatedEquidimensional`, following the landing checker's return
at c08d7e55b. This preserves the downstream availability of `closureInclusion` identified
for `Sheaf.AlgebraicGeometry.HighGenusHomClosure`; that consumer is not edited.

## Old

The existing public namespace opens and options were:

```lean
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
```

The public theorem signature is retained verbatim:

```lean
theorem flat_fibre_component_closure_dimension
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (t s : S) (B : Set (f.fiber t))
    (hB : B ∈ irreducibleComponents (f.fiber t))
    (y : f.fiber t) (hy : IsGenericPoint y B) :
    ∀ (D : Set
      (Set.inter (closure ({f.fiberι t y} : Set X)) ((f.base : X → S) ⁻¹' ({s} : Set S)))),
      D ∈ irreducibleComponents
        (Set.inter (closure ({f.fiberι t y} : Set X)) ((f.base : X → S) ⁻¹' ({s} : Set S))) →
      topologicalKrullDim D = topologicalKrullDim B
```

## New

The same public theorem signature and public imports. Added file-local elaboration commands:

```lean
open TopologicalSpace TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

They allow the standard ringed-space/sheaf coercions in private proof helpers to elaborate.
No imported module inherits namespace opens or elaborator transparency options from this file.
The existing sorry body is replaced by the pointwise 0GSI argument and proved private helpers.

## Users

`tools/downstream.py --uses flat_fibre_component_closure_dimension` found 91 downstream
modules; its textual-use list contains only the item itself. The table includes every
downstream module and that textual-use entry. None is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.HighGenusHomClosure | NB | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalCurveLCICriterion | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalCurveStackSmooth | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalTraitRegularization | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.PersistentNodeNormalization | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No interface change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No interface change; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No interface change; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No interface change; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | No interface change; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | No interface change; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular | unclaimed | No interface change; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | Q114 | No interface change; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry | A5 | No interface change; no adaptation. |
| Sheaf.TraceFormula.BaseModificationComparisonFibreImage | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.NoIsolatedContractedFibreComponent | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.NodalFamilyNoetherianApproximation | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.ValuativeDominationEtaNormal | unclaimed | No interface change; no adaptation. |
| Sheaf.TraceFormula.FlatFibreComponentClosureDimension (1) | unclaimed | No interface change; no adaptation. |

## Status

landed 20261023T131738-L-2145724 2026-10-23 (merge of deliver/Q7/Sheaf.TraceFormula.FlatFibreComponentClosureDimension)

# WeilConjectures.local_graded_flat_module_finite_presentation

## Reason

The completed proof uses tensor-product notation in private helpers and its theorem body.
It adds `open scoped TensorProduct` inside `namespace WeilConjectures`. The preflight
command comparison classifies this additional command as an interface change, so this
record documents the command and checks its consumers. Opening the existing notation
scope changes name resolution within this file; it introduces no exported notation,
attribute, instance, public declaration or changed definition. All original public imports
and the theorem signature remain verbatim. Every added helper is private and proved.
No consumer adaptation or target statement review is required.

## Old

The namespace began as follows, without a scoped notation opening:

```lean
namespace WeilConjectures
```

The public theorem signature was:

```lean
theorem local_graded_flat_module_finite_presentation
    {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i : Fin n, 0 < ω i)
    {L : Type v} [AddCommGroup L] [Module (MvPolynomial (Fin n) R) L] [Module R L]
    [IsScalarTower R (MvPolynomial (Fin n) R) L]
    (Ldeg : ℤ → Submodule R L) (hLinternal : DirectSum.IsInternal Ldeg)
    (hgraded : ∀ (e d : ℤ) (p : MvPolynomial (Fin n) R) (x : L),
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i : Fin n ↦ (ω i : ℤ)) e →
      x ∈ Ldeg d → p • x ∈ Ldeg (e + d))
    [Module.Finite (MvPolynomial (Fin n) R) L] [Module.Flat R L] :
    Module.FinitePresentation (MvPolynomial (Fin n) R) L
```

## New

The namespace now begins:

```lean
namespace WeilConjectures

open scoped TensorProduct
```

The public theorem signature is unchanged:

```lean
theorem local_graded_flat_module_finite_presentation
    {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i : Fin n, 0 < ω i)
    {L : Type v} [AddCommGroup L] [Module (MvPolynomial (Fin n) R) L] [Module R L]
    [IsScalarTower R (MvPolynomial (Fin n) R) L]
    (Ldeg : ℤ → Submodule R L) (hLinternal : DirectSum.IsInternal Ldeg)
    (hgraded : ∀ (e d : ℤ) (p : MvPolynomial (Fin n) R) (x : L),
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i : Fin n ↦ (ω i : ℤ)) e →
      x ∈ Ldeg d → p • x ∈ Ldeg (e + d))
    [Module.Finite (MvPolynomial (Fin n) R) L] [Module.Flat R L] :
    Module.FinitePresentation (MvPolynomial (Fin n) R) L
```

## Users

`tools/downstream.py Sheaf.RingTheory.LocalGradedFlatModuleFinitePresentation
--uses WeilConjectures.local_graded_flat_module_finite_presentation` found 111
transitive importers and no theorem-name occurrences in those importers. Its sole
name occurrence is the declaration in the item itself. The direct parent
`Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation` still has its planned
application in an unfinished proof. Its planned application remains valid because the
signature is identical. No downstream file is changed by this delivery. The table
includes all transitive importers; holders are the current local claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.LocalGradedFlatModuleFinitePresentation | K9 | Proof completed; public signature unchanged. |
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.GenericFreeBlowup | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.HighGenusHomClosure | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalCurveLCICriterion | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalCurveStackSmooth | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.NodalTraitRegularization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.PersistentNodeNormalization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry | A5 | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.BaseModificationComparisonFibreImage | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FlatAssociatedEquidimensional | X6 | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FlatFibreComponentClosureDimension | Q7 | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FlatFibreFreeNeighbourhood | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | E4 | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | P8 | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.NoIsolatedContractedFibreComponent | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.NodalFamilyNoetherianApproximation | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationFiniteModuleInjectivity | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationFlatFiniteModulePresentation | E6 | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Unaffected; no exported signature or definition changes. |
| Sheaf.TraceFormula.ValuativeDominationEtaNormal | unclaimed | Unaffected; no exported signature or definition changes. |

## Status

landed 20261023T123837-L-1266070 2026-10-23 (merge of deliver/K9/Sheaf.RingTheory.LocalGradedFlatModuleFinitePresentation)

# AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_quotient_killing_kernel_germ

## Reason

The complete proof uses the opposite-category and topology namespaces and caches
standard slice-site instances to keep elaboration within the single-file limit.
The conservative interface checker records the added `open` and `set_option`
commands, and the instance checker flags the seven private instances for review.
All seven instances are private and proved. No public declaration signature,
public import, exported attribute, target meaning, or definition changes.
No source-library module is edited.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

The declaration signature, verbatim:

```lean
theorem exists_finitePresentation_quotient_killing_kernel_germ
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (G F : X.Modules) [SheafOfModules.IsFinitePresentation.{u} G]
    [SheafOfModules.IsQuasicoherent.{u} F] (α : G ⟶ F)
    (x : X) (s : (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).obj G.val)
    (hs : (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).map α.val s = 0) :
    ∃ (K : X.Modules) (ι : K ⟶ G),
      Mono ι ∧ SheafOfModules.IsQuasicoherent.{u} K ∧ SheafOfModules.IsFiniteType.{u} K ∧
        (∀ (U : X.Opens) (t : Γ(K, U)), α.app U (ι.app U t) = 0) ∧
        SheafOfModules.IsFinitePresentation.{u} (cokernel ι) ∧
        (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).map
          (cokernel.π ι).val s = 0 ∧
        ∃ β : cokernel ι ⟶ F, cokernel.π ι ≫ β = α
```

## New

```lean
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
```

The declaration signature is exactly the signature in `Old`. The theorem's single
`sorry` is replaced by the complete proof. Private helpers provide the explicit
restricted section, its finite-type carrier, and quasi-coherence of slice images.
The seven private instances are `sliceHasSheafify`, `sliceHasWeakSheafify`,
`doubleSliceHasSheafify`, `doubleSliceHasWeakSheafify`, `sliceLocallyBijective`,
`doubleSliceLocallyBijective`, and `sliceAbelian`. Their proofs obtain existing
standard instances; no mathematical structure or public instance is changed.
All elaboration commands affect only this file.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FinitePresentationKernelGermEffacement
--uses exists_finitePresentation_quotient_killing_kernel_germ` reports 52 downstream
modules and two textual users (the declaring module and
`Sheaf.AlgebraicGeometry.ModuleFilteredColimitFinitePresentation`). The latter's
existing call is reviewed against the identical signature. Every downstream
statement keeps exactly the same meaning, since only the theorem proof and
private helpers change. No consumer is adapted. The full downstream list follows;
holders are the current claim records at packet preparation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationKernelGermEffacement | Q3 | Complete proof; unchanged public signature. |
| Sheaf.AlgebraicGeometry.AlgebraDirectedColimitFiniteType | T6 | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite | P8 | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ModuleFilteredColimitFinitePresentation | unclaimed | Direct theorem use reviewed; same hypotheses and conclusion; no adaptation needed. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Unchanged statement and imports; no adaptation needed. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Unchanged statement and imports; no adaptation needed. |

## Status

landed 20261023T131724-L-2143794 2026-10-23 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.FinitePresentationKernelGermEffacement)

# AlgebraicGeometry.standardSingleFlatCounit_localization_presentation_data

## Reason

Restore the missing source named by this item's `coord/rework.tsv` row from
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationPresentationData.lean`.
The source was quarantined after the 2026-10-20 cluster rollback. Its DAG attachment
and the archived localization parent still require the theorem. The archive is
preserved. This is a zero-hole source restoration, not a new proof or decomposition.

The two dependencies have been restored independently: the presentation predicate
by B3 and the top-open comparison by C4. The entire archived item, including both
private helpers, the public theorem, both imports, options and docstrings, compiles
unchanged against the current published library. The source is restored verbatim;
no definitions, signatures or target statements change.

## Old

The current `lean/` source path is absent. The preserved quarantine source has the
following public signature and its complete proof:

```lean
theorem standardSingleFlatCounit_localization_presentation_data
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∃ (S : B.Opens) (V : A.Opens), g a ∈ S ∧ a ∈ V ∧
      IsAffine S.toScheme ∧ IsAffine V.toScheme ∧
      ∃ hVS : V ≤ g ⁻¹ᵁ S,
        StandardSingleFlatCounitPresentation (p ∣_ S)
          (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS)
```

## New

The same signature above, the complete archived proof and both private helpers are
restored verbatim at the node's existing `lean.file`. No arbitrary object is chosen
from an unproved existence theorem: all presentation witnesses are unpacked and
reassembled within this existential theorem.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData
--uses standardSingleFlatCounit_localization_presentation_data --allow-missing`
reports zero current live source consumers. A reverse-import scan of both library
roots and their quarantine archives, with live source overriding an archive of the
same module, finds 1 direct consumer and 77 transitive consumers.
They are listed below with claim holders at inspection. The direct archived caller
compiles unchanged against the restored theorem in 5.1 seconds. The restored item
compiles cleanly in 7.8 seconds, and its axiom probe reports exactly `propext`,
`Classical.choice` and `Quot.sound`. No consumer needs adaptation,
since the entire public interface and public imports are identical to the archive.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData | F1 | Restore the complete proved module from quarantine. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | Direct consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive consumer; identical interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive consumer; identical interface, no adaptation. |

The node `lem-pc-standard-single-flat-counit-localization-presentation-data` keeps
its Lean attachment, statement and four-step proof plan. Its parent
`lem-pc-standard-single-flat-counit-localization` still uses the local affine
presentation. The unit `sk-thm-picard-coherence` and target meanings do not change.
The current Lean import closure does not justify pruning this DAG-required module.

## Status

landed 20261021T014703-L-2444345 2026-10-21 (merge of deliver/F1/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData)

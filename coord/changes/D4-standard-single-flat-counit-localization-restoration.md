# AlgebraicGeometry.standardSingleFlatCounit_localization

## Reason

Restore the exact missing source named in `coord/rework.tsv`, row for
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization`, from
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalization.lean`.
The recorded cluster rollback quarantined a proved module; its absence is not
withdrawal. The archive and its existing DAG attachment are preserved.

Both declared dependencies now exist in the live library. The archived proof
first obtains affine neighbourhoods and their actual localized presentation from
`standardSingleFlatCounit_localization_presentation_data`, then applies
`standardSingleFlatCounit_localization_completion` to those same witnesses.
Restoring the source repairs the missing declaration without changing its type,
universe, visibility, public import, docstring, proof or definitions. This is a
zero-hole restoration, with no proof or decomposition credit claimed.

## Old

The live source path is absent. The preserved quarantine source has this exact
public theorem signature, followed by its complete proof:

```lean
theorem standardSingleFlatCounit_localization
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) ∧
        ∀ n : ℤ,
          ∃ (eL : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
              ((DerivedCategory.homologyFunctor _ n).obj
                ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
                  ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
              (DerivedCategory.homologyFunctor _ n).obj
                (LF.obj (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ eR.hom
```

## New

Restore that same signature and the complete archived file verbatim at
`lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalization.lean`.
Every byte equals the quarantine archive. The sole public import remains
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation`; both private proof
imports remain the presentation-data and completion modules. No node field
changes: the existing two proof steps and proof dependencies already describe
this exact proof. No source-library declaration or target statement changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization
--uses standardSingleFlatCounit_localization --allow-missing` reports zero live
source consumers. A reverse import scan including both library roots and their
quarantine archives, with live sources taking precedence, finds one direct
archived consumer and 76 total transitive consumers. They are listed below with
claim holders from the shared snapshot.

The restored item compiles cleanly in 5.6 seconds; a separate axiom probe reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. The original archived
direct consumer `StandardSingleStalkFlatCounitModel` independently fails at lines
79 and 92: its public scalar-extension homotopy functors lack an `Additive`
instance. Its public import
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` is a withdrawn empty
module; the proved instance provider now lives at
`WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
In scratch only, adding that upstream public import makes the entire original
consumer statement and proof compile unchanged against the restored item in
4.5 seconds. Thus its theorem application and the complete original argument
remain compatible. The consumer's import restoration is separate rework, not
an adaptation forced by this unchanged theorem. No scratch files are delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed in shared snapshot | Restore the complete archived theorem unchanged. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed in shared snapshot | Direct archived caller; same statement and theorem call; separate stale import. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed in shared snapshot | Transitive consumer; identical interface and meaning, no adaptation. |

## Status

landed 20261021T020104-L-2584318 2026-10-21 (merge of deliver/D4/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization)

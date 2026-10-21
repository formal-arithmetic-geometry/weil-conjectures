# AlgebraicGeometry.exists_standardSingle_stalk_flat_counit_model

## Reason

Restore the quarantined module assigned by `coord/rework.tsv`, preserving its theorem,
proof, and DAG attachment `lem-pc-standard-single-stalk-flat-counit-model`.
The archive fails to compile at lines 79 and 92 with:

```text
failed to synthesize instance of type class
  (ModuleCat.extendScalars (CommRingCat.Hom.hom (Scheme.Hom.stalkMap g a))).Additive
```

The old public import is now a withdrawn empty module. Its upstream replacement
provides the proved `ModuleCat.baseDerivedTensor_extendScalars_additive` instance
needed in the public theorem's homotopy scalar-extension functors. The existing
D4 localization restoration record had independently diagnosed the same defect.

## Old

The archived public import was:

```lean
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The existing theorem signature, preserved verbatim, is:

```lean
theorem exists_standardSingle_stalk_flat_counit_model
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

Restore the whole archive at
`lean/Sheaf/AlgebraicGeometry/StandardSingleStalkFlatCounitModel.lean`, with exactly
one changed line:

```lean
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The theorem signature and proof are byte-identical to the archive. The new import
is public because its additive instance is needed to elaborate the public signature.
The affine, union, localization, and quasi-compact-open induction proof is retained.
The node's existing attachment and proof route remain correct, so no node field changes.
There are no definition changes and no changes to a target's mathematical meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel
--uses exists_standardSingle_stalk_flat_counit_model --allow-missing` finds zero live
consumers. A reverse import scan of both library roots together with their quarantine
archives, taking live sources in preference to archived copies, finds 1 direct
archived consumer and 75 total transitive consumers including that direct
consumer. The complete list and current claim holders are below.

The original archived direct consumer
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi` compiles unchanged against
the repaired item in one `lcompile.py --all` run. That consumer was used only for
validation and is not delivered. The item compiles cleanly in 4.9 seconds; the
explicit `#print axioms` run takes 5.9 seconds and reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The consumer compiles in 0.4 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Direct archived consumer; original compiles unchanged against restored item. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | T7 | Restore the archived theorem; repair its public instance-provider import. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive archived consumer; identical theorem type and meaning; no adaptation. |

## Status

landed 20261021T182549-L-1224561 2026-10-21 (merge of deliver/T7/Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel)

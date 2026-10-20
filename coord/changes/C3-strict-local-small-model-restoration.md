# AlgebraicGeometry.Etale.nonempty_strictLocalBaseChange_continuityPresentation

## Reason

Repair the restored rework item without changing its original small-colimit-model statement.
The live file imports canonical-model source helpers alongside original-model Sheaf interfaces.
Single-file compilation fails on the duplicate
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq` supplied by
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` and
`WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension`.
The source helpers use `strictLocalization` and `strictLocalizationToBase`; the assigned
statement uses `strictHenselizationScheme` and `strictHenselizationStructuralMap`.
They cannot be substituted by definitional equality.

Restore the 24 fully proved `StrictLocalSmallModel` counterparts previously landed in
c03b8450536 and dropped by batch recovery. The item retains its entire original statement,
public imports, geometry/germ/injective-representative route and assembly argument.
Its three private imports and their calls now use those original-model helpers.
The existing DAG nodes attach to the restored implementations. No source-library declaration,
attribute, public import or proof is changed. No archived source is deleted or withdrawn.

## Old

```lean
theorem nonempty_strictLocalBaseChange_continuityPresentation {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) (n : ℤ) : Nonempty (GlobalCohomologyContinuityPresentation X K n ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology AddCommGrpCat.{v + 1}).map ((DerivedCategory.Plus.homologyFunctor _ n).map ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1} (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)) |>.natTrans.app K))))
```

Private imports:
```lean
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologySourceColimit
import WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionFormulas
```

## New

```lean
theorem nonempty_strictLocalBaseChange_continuityPresentation {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) (n : ℤ) : Nonempty (GlobalCohomologyContinuityPresentation X K n ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology AddCommGrpCat.{v + 1}).map ((DerivedCategory.Plus.homologyFunctor _ n).map ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1} (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)) |>.natTrans.app K))))
```

Private imports:
```lean
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas
```

The three existence/colimit calls receive the `smallModel_` prefix. Their statements
refer to the original Sheaf geometry, germs and projection data. Each restored helper
follows the existing upstream proof using the original spectrum, structural morphism,
cone and cofilteredness theorem. All restored theorem proofs are complete. Every restored
module is transitively imported by the item; no additional hypothesis or cohomological
restriction is introduced. The geometry continues to use the proved original-model
`strictHenselizationBaseChangeCone_exists`. No target meaning changes.

Restored modules under `Sheaf.AlgebraicGeometry.StrictLocalSmallModel`:

| module suffix | public declarations |
| --- | --- |
| DerivedCohomologyGermIso | smallModel_isIso_strictLocalCohomologyGermMap |
| InjectiveExchangeRepresentative | smallModel_injectiveExchange_representative |
| InjectiveExchangeSourceTransport | smallModel_injectiveExchange_source_transport |
| InjectiveExchangeTargetTransport | smallModel_injectiveExchange_target_transport |
| SourceCocycleExactRestriction | smallModel_sourceCocycleExactRestriction |
| SourceDerivedSectionsNaturality | smallModel_sourceDerivedSections_naturality |
| SourceDerivedSectionsNaturalityCore | smallModel_sourceDerivedSections_naturality_core, smallModel_sourceDerivedSections_naturality_evaluation, smallModel_sourceDerivedSections_naturality_compose |
| SourceLocalizedCocycleHomology | smallModel_sourceCocycleHomologySection, smallModel_sourceLocalizedCocycleHomology |
| SourceStageSectionsNaturality | smallModel_sourceStageSectionsIso_naturality |
| StrictLocalCohomologySourceColimit | smallModel_isColimit_strictLocalCohomologySourceLegs |
| StrictLocalComplexSectionsMate | smallModel_strictLocalComplexSectionRestriction_mate |
| StrictLocalDerivedExchangeGlobalSections | smallModel_strictLocalDerivedExchange_globalSections |
| StrictLocalDerivedExchangeLeray | smallModel_strictLocalDerivedExchange_leray |
| StrictLocalDerivedMateSectionsFactorization | smallModel_strictLocalComplexSectionRestriction_derivedMate |
| StrictLocalInjectiveSourceComparison | smallModel_sourceFreeSectionsEquiv, smallModel_sourceFreeSectionsEquiv_comp, smallModel_sourceFreeSectionsComplexIso, smallModel_sourceInjectiveDirectImageIso, smallModel_sourceClassDerivedHomIso, smallModel_sourceStageSectionsIso, smallModel_sourcePlusHomIso, smallModel_strictLocalInjectiveSourceIso |
| StrictLocalInjectiveSourceDerivedRestriction | smallModel_strictLocalInjectiveSourceIso_derivedRestriction |
| StrictLocalInjectiveSourceRestriction | smallModel_strictLocalInjectiveSourceIso_restriction |
| StrictLocalInjectiveSourceSections | smallModel_exists_strictLocalInjectiveSourceSections |
| StrictLocalInjectiveSourceTransition | smallModel_strictLocalInjectiveSourceIso_transition |
| StrictLocalLocalizedHomGerm | sourceLocalizedSectionsIso, smallModel_strictHenselizationSectionRestriction_naturality, strictLocalSectionRestrictionNat, strictLocalComplexSectionRestriction, smallModel_sourceLocalizedSectionsIso_germ |
| StrictLocalMateProjectionFormulas | smallModel_nonempty_strictLocalMateProjectionData |
| StrictLocalNeighbourhoodGeometryExistence | smallModel_nonempty_strictLocalNeighbourhoodGeometry |
| StrictLocalSectionsUnitLeray | smallModel_strictLocalSections_unit_leray |
| StrictLocalUnderivedSectionsMate | smallModel_strictLocalUnderivedMateSections, smallModel_strictLocalUnderivedMateSections_eq |

The localized Hom module initially exceeded the 60-second single-file limit.
Profiling identified expensive unfolding of inverse-image and derived-Hom constructions.
The restored module locally marks the three imported comparison constructions irreducible,
and its sourceLocalizedSectionsIso definition shares the free sheaf, single complex and
homology functor using let bindings. This preserves the definition by definitional equality
and keeps every consumer signature unchanged. No limit is raised and no file is split.

## Users

The following is the complete current transitive census from tools/downstream.py.
Only `StrictLocalBaseChangeGlobalHomology` imports the item directly. That source is
compiled unchanged against the repair. Since the item's signature and all its public
imports stay verbatim, the other users receive the identical interface. No existing
consumer is adapted; no forced adaptation is submitted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomologyStalk | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnitGerm | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.OpenComplementKnown | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.AffineInfinityBoundarySupport | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialHigherProjectionSupport | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialInductionStep | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialProjectionSupport | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeTargetStalkIso | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreDerivedUnit | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreUnitStalks | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalGeometricFibreTest | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.FiniteAffineDirectImageSupportBound | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity | unclaimed | Unchanged signature, public imports and proof; no edit required. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.* | new/restored, C3 | Complete proof dependency chain; no prior live importers. |

## Status

landed 20261020T233100-L-891847 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation)

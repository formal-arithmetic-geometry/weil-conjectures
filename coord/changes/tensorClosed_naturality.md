# SheafOfModules.tensorClosed

## Reason

The fetched baseline makes tensorClosed a compatibility abbreviation rather
than a theorem. The interface checker records any abbreviation body edit,
including this explicit naturality proof calculation. Both bodies prove the
identical proposition and are definitionally equal by proof irrelevance.
The existing monoidalClosed and tensorHomEquiv constructions remain the
witnesses. No definition of tensor or internal Hom changes, and no target
meaning changes. No adapted module is necessary: every old use receives the
same proposition, with definitionally equal proof terms. This record is for
the conservative interface check, not a change of mathematical statement.

## Old

```lean
abbrev tensorClosed (R : Sheaf J CommRingCat.{u}) :
    letI := monoidalCategory R
    letI := symmetricCategory R
    Nonempty (MonoidalPreadditive (SheafOfModules.{u} (𝓡 R))) ∧
      Nonempty (MonoidalClosed (SheafOfModules.{u} (𝓡 R))) ∧
        ∃ e : ∀ (F G H : SheafOfModules.{u} (𝓡 R)),
            (F ⊗ G ⟶ H) ≃ (G ⟶ homObj F H),
          ∀ (F F' G G' H H' : SheafOfModules.{u} (𝓡 R))
            (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H') (t : F ⊗ G ⟶ H),
            e F' G' H' ((f ⊗ₘ g) ≫ t ≫ h) =
              g ≫ e F G H t ≫ homObjMap f h := by
  let := monoidalCategory R
  let := symmetricCategory R
  refine ⟨⟨?_⟩, ⟨monoidalClosed⟩, tensorHomEquiv, ?_⟩
  · exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  · intro F F' G G' H H' f g h t
    rw [tensorHom_def, Category.assoc, tensorHomEquiv_whiskerRight_comp,
      tensorHomEquiv_whiskerLeft_comp, tensorHomEquiv_comp_homObjMap]
    -- Reassociate the induced internal-Hom maps and cancel identities.
    simp only [Category.assoc, homObjMap_comp_homObjMap, Category.comp_id]
```

## New

```lean
abbrev tensorClosed (R : Sheaf J CommRingCat.{u}) :
    letI := monoidalCategory R
    letI := symmetricCategory R
    Nonempty (MonoidalPreadditive (SheafOfModules.{u} (𝓡 R))) ∧
      Nonempty (MonoidalClosed (SheafOfModules.{u} (𝓡 R))) ∧
        ∃ e : ∀ (F G H : SheafOfModules.{u} (𝓡 R)),
            (F ⊗ G ⟶ H) ≃ (G ⟶ homObj F H),
          ∀ (F F' G G' H H' : SheafOfModules.{u} (𝓡 R))
            (f : F' ⟶ F) (g : G' ⟶ G) (h : H ⟶ H') (t : F ⊗ G ⟶ H),
            e F' G' H' ((f ⊗ₘ g) ≫ t ≫ h) =
              g ≫ e F G H t ≫ homObjMap f h := by
  let := monoidalCategory R
  let := symmetricCategory R
  refine ⟨⟨?_⟩, ⟨monoidalClosed⟩, tensorHomEquiv, ?_⟩
  · exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  · intro F F' G G' H H' f g h t
    rw [tensorHom_def, Category.assoc]
    calc
      tensorHomEquiv F' G' H' (f ▷ G' ≫ F ◁ g ≫ t ≫ h) =
          tensorHomEquiv F G' H' (F ◁ g ≫ t ≫ h) ≫ homObjMap f (𝟙 H') :=
        tensorHomEquiv_whiskerRight_comp f _
      _ = (g ≫ tensorHomEquiv F G H' (t ≫ h)) ≫ homObjMap f (𝟙 H') := by
        rw [tensorHomEquiv_whiskerLeft_comp]
      _ = g ≫ tensorHomEquiv F G H t ≫ homObjMap f h := by
        rw [tensorHomEquiv_comp_homObjMap]
        simp only [Category.assoc, homObjMap_comp_homObjMap, Category.comp_id]
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarRestrictedTensorRetractFlat | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.AcyclicKFlatTensor | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.BoundedFlatReplacement | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.FilteredColimitsTensorTotal | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.FlatAugmentationEpicification | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.KFlatClosure | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.KFlatTelescopeClosure | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.KFlatTensorProduct | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.KFlatTensorQuasiIso | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.OpenRestrictionKFlat | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.OpenRestrictionTensorHomology | unclaimed | unchanged: proof irrelevance |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.AffineKoszulSectionColimit | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.BoundedComplexTensorProperSupportBound | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedAdjoint | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedLocalizationTensorComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedResidueUnitBetti | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedTensorAugmentation | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedTensorHomSectionsUnit | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedTensorRightCoproducts | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedTensorStructure | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedTensorSymmetry | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.DerivedTensorUpperBound | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.FieldFibreHomology | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.FlatModuleCanonicalDerivedPullbackAux | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.FlatModuleTilde | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | Q3 | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.KFlatBifunctorIsoDescent | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.KFlatSingleTensorRepresentative | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.KFlatTensorModelNaturalComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectCounit | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OpenScalarRestrictionStalkCriterion | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentOverTransport | H4 | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationData | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferential | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverComparisons | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTransport | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationPostDifferential | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationPreDifferential | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationPrecompositionNaturality | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationTensorSummands | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyBounded | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PerfectHypercohomologyGap | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PicardTermwiseTargetCoherence | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.QCqsProjectionMateAffineLocus | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.QCqsProjectionMateShiftedUnit | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap | D2 | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeTensorEvaluationLocalizationCoherence | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SchemeTensorUnitAction | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.SpectrumStructureRestrictionComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalCohomology | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TensorCoordinateIdentifications | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.TotalTensorOverEquivIso | unclaimed | unchanged: proof irrelevance |
| Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.CechCupResolutionComparisonExists | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalSectionsLaxMonoidalData | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackDerivedData | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackKFlat | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackMatesIsIso | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackOplaxIsIso | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackTensorDescent | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.GlobalTensorPullbackUnderivedData | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupAdjunctionPolygon | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupCoefficientResolutionMaps | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | Q3 | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupGlobalTensorComparison | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupGlobalTensorPullback | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupGodementPairing | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupKInjectiveTarget | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupNaiveMap | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupPairingExists | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupRealizationComplexData | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed | unchanged: proof irrelevance |
| Sheaf.Paper.ModuleCupResolutionInvariance | unclaimed | unchanged: proof irrelevance |

All listed users keep their existing signatures and implementations. The
abbreviation has a Prop-valued result, so different proofs of that result
are definitionally equal. The change cannot select different tensor or
closed data: it changes only the proof of the same conjunction.

## Status

landed 20261014T022539-L-4043357 2026-10-14 (merge of deliver/A3/Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed)

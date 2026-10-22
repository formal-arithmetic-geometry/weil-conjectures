# ProjectionRestriction declarations: separate data from proof assembly

## Reason

Construction lemmas must refer to the normalized Global and Local types. Keeping those types
in the same module as the theorem that imports the construction lemmas creates an import cycle.
Move the data, unchanged, to RingedProjectionRestrictionData and publicly import it from the
original module. This is a dependency separation, not a compile-time workaround. The original
module already compiled within the limit. No target statement or definition meaning changes.

The entire exposed declaration block (from `@[expose] public noncomputable section` through
`Local.ProjectionCompatible` and its namespace close) was compared byte-for-byte with the
original source; it is identical. All original six public imports remain public through Data.
Only unused private imports and the module-level prose were changed.

Return-repair note (head `870ff0b861f`): this record is delivered at
`coord/changes/ringed-projection-restriction-data.md`. If the reviewer supplies
an override through stage-3 `--apply-fixes`, the merge tool's required alias is
`ringed-projection-restriction-data.change.md`, not the bare `.md` filename.
The earlier failed landing did not change the mathematical review result.

## Old

`Sheaf.Paper.RingedProjectionRestriction` defines the data declarations and then states
`AlgebraicGeometry.Scheme.ringedProjectionRestriction` in the same module. The representative
public declaration is verbatim below.

```lean
structure TensorModel (R : Sheaf J CommRingCat.{u + 1}) where
  preadditive : @MonoidalPreadditive (Mod R) _ _ (SheafOfModules.monoidalCategory R)
  functor : Der R × Der R ⥤ Der R
  representative : ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q ≅
    (((resolving R).ι ⋙ DerivedCategory.Q).prod
      ((resolving R).ι ⋙ DerivedCategory.Q)) ⋙ functor
  /-- Natural transformations are determined on all flat K-flat representatives. -/
  descent : ∀ (F G : Der R × Der R ⥤ Der R), Function.Bijective
    (fun t : F ⟶ G ↦ Functor.whiskerLeft
      (((resolving R).ι ⋙ DerivedCategory.Q).prod
        ((resolving R).ι ⋙ DerivedCategory.Q)) t)
```

## New

`Sheaf.Paper.RingedProjectionRestrictionData` defines the identical declarations, with the
same names, universes, instances, visibility and bodies. The original module has
`public import Sheaf.Paper.RingedProjectionRestrictionData` and retains the identical theorem
signature. In particular the `TensorModel` declaration above is also the new declaration,
verbatim. No wrapper, new choice, or alternative definition is inserted.

The main DAG attachment now owns the assembly theorem. The existing general-operation node
points to Data, and the new data node records the remaining unchanged normalized interfaces.

## Users

Refreshed on 2026-10-22 from current source imports and DAG dependency records.
The table covers all current direct and transitive importers, packet modules,
and recorded future consumers along statement/proof dependency paths. Rows
marked as planned DAG consumers are conservative additions; they do not assert
a current Lean import. All public data signatures, bodies and instances stay
identical and publicly reachable, so no consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BoundedAboveCoherentRHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.CompleteLocalCoherentDuality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorLinearEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.RingedOpenFlatResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.RingedSliceHomSourceShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.SemidualizingRHomConservative | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.SitePerfectScalarHomComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AdicClosedImmersionFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineOpenStrictLocalCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineOpenStrictLocalConstantBound | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineOpenStrictLocalConstructibleCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceConstruction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ClassicalSupportCounitIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.CoconeDerivedComparisonNormalForm | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ConormalConeHomExt | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteMapAffineLine | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.Curve.H1DualTateModule | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCurveCompatibleH1NoFixed | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.Curve.SepclosedRegularProperTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeArrowLocalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EquivariantMarkedNodalAlteration | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCoordinateSupport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleInjectiveFiniteCechRows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSiteBoundedConstantModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentEtaleConstantProjection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionScalarTransportData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionTransportData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleLocalizationComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleReverseAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatRegularDivisorPurityDescent | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldDual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldSitePerfect | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.CompactCharacterLogarithm | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1 | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.WeilTwistedPaths | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.GabberPartialAlgebraization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.GabberPrimeToEllRegularCover | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.KummerRootRegularDivisorPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.LocalDimensionFunctionCalculus | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.NodalFamilyEtaleSourceLocality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianAffineLineUnit | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.OpenClosedConstructibleTest | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison | Q8 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.OriginComparisonArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.PicardRiemannRoch | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PrimePowerHomTensorTest | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PrimeToEllUniformizationStandardForm | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtalePairFlasque | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedProductNaturality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroupDevissage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroupPrimeCases | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperDirectImageComparisonFinitude | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperGenericCurvePreparation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.PunctualPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PunctualPurityEtaleLocality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PunctualPurityProperDegreeDescent | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PunctualPurityTwoOfThree | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PuncturedPerverseHighComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PurSupportExact | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PurityAffineLineComponents | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.PurityRelativeCone | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.QuasiExcellentEtaleDirectImageFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ReesConeNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RegularDimensionFunctionPullback | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RegularImmersionLinearization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RegularNormalCrossingsConstantImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RegularSpecializationGeometry | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RelativeSingleTensorCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPresentationCokernel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SectionReesNoetherianGeometry | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SemistableCoordinateDivisorPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SfFullCdWeaklyContractibleTest | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportLocalizationTriangle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportTriangleCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportTriangleConstruction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientComplexOpenTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientDerivedOpenMate | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientOpenMateQuotient | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientOrdinaryOpenTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientOrdinarySecondOpenTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientTensorQuotientSquare | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedExteriorProduct | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedExteriorProductBoundary | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedExteriorProductSupportMaps | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedProductForgetSupports | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedProductQuotientModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedProductSupportCongruence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.SupportedTensorComparisonNaturality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.TransverseGysinLimit | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.UniformizationNodalQuotientReduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenUnitCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingPullbackUnitCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingTensorComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingTensorSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.VectorExtensionSplittingCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.CechLocalizationUnitTotalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedActionModule | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedActionTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedCup | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInflationArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInvariantBar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInvariants | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedEquivariantBarData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedInternalBarResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedNormalInvariantData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedNormalSubgroupComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedProductActionInflation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedProductBarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedScalarTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedSplitCosetInduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.CondensedUnipotentClass | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.ContinuousScalarRing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.DiscreteLatticeCupExterior | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.EquivariantResolutionBarNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.FiniteFreeCompletionTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.InternalBarOrderedCup | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.InternalBarRoofAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.InternalInflationGradedCup | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.LatticeAlgebraDerivedCup | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.LatticeRestrictionCupComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.LocalizedModuleExactForSystems | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.LocalizedModuleExactIndependent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.NormAlgclBarAugmentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.NormedScalarProfiniteHomAcyclic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.PolynomialDerivedBarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.PolynomialTranslationAcyclic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.ProfiniteActionParameters | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.ProfiniteInvariantsFilteredContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeBarData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeCyclicRestrictionModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeCyclicTotal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeDerivedInvariants | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeInvariantForgetting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeLatticeBridge | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RelativeTrivialCyclicMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedCechCompletionHomInjective | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedCechKoszulDualLimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedCompleteTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedKoszulCompletionReflector | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedSitePerfectDualityForModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.RingedSiteSignedDualRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.ScalarLocalizationMonoidal | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.StageSystemKaroubi | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.CategoryTheory.SubterminalCoverModuleSES | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.SubterminalModuleLocalCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Compactification.NagataDensityNormalizationSheaves | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.NumberTheory.Padics.CoefficientExtensionSmallLog | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.NumberTheory.Padics.DeepPrincipalUnitLog | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ActualCompletedReductionReconstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicCohomologyTorsionNormalForm | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicCompleteHomSections | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicCompleteReductionCone | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicCompleteResidueConservative | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicFiniteExchangeEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPerfectModelCompleteReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPerfectReductionHomML | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicResidueFiniteLocalModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicResidueLiftComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicResidueLissePerfectLift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicStratumCompletionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicStratumCoverConservativity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicTorFlatCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdicTorFlatCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdmissibleScalarRealizationExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineLineSupportGeometry | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AmplificationProper | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryBoundedTensorComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryExceptionalComparisonData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryQDefiningCompositeComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundedBelowCtfReflection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundedFiniteModelGeneration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CanonicalCoefficientSystemGeometry | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CanonicalOpenRestrictionModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | P2 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClassicalLocalizationTriangleTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ClosedFiniteAdjointCounitTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ClosedIdentityOpenHomNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClosedSupportedScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ClosedTestDerivedExchangeModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientCohomologyModules | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExtensionFiniteAssociation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExtensionReductionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExtensionReductionModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExtensionRepresentativeRoos | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExtensionRestrictedTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientExtensionStrictRepresentatives | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientFrobenius | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoefficientRealizationTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CohomologicalSmoothnessFiniteComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CohomologyTorInterval | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CommonStageLisse | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonTensorComparisonConstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonTensorComparisonDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CommonTensorComparisonRepresentatives | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactAdicContinuousIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportCoefficientTransition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactSupportDirectImageTriangulated | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactSupportExchangeTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportIntrinsicTensorComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportNativeSystemEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportNativeSystemTransition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportSiteCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactificationCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactificationProjectionPasting | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ComparisonTorAmplitude | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompleteGroupTorsorMonodromy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompleteProetale | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedCoefficientCompletionRoosTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedCoefficientPullbackLinearity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompletedDirectImageLimits | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedExchangeCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedExchangeUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedExtensionZeroComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedFiniteComparisonModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedIntegralQuotientModelComparison | F3 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedIntegralScalarData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedKoszulQuotientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedLineComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedLineDerived | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedLineTensorCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOpenFiniteEtaleOrigins | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOpenKFlat | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOrdinaryComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedOrdinaryExchangeCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPullbackAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPullbackReduction | E4 | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompletedPullbackReflection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedPullbackUnitTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedRealizationDerivedCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedReductionPullbackSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | M3 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedScalarChainShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedScalarShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedScalarShiftDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedScalarUnitAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedStrictOpenExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedTensorUnitInsertion | E8 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletionFiniteReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletionMateComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CompletionTriangleComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompletionUnitFiniteProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ConcentratedComplexShift | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedLocalizationHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedOpenExtensionProducts | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedPointSupertrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedScalarFinitePresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantDerivedLimitResolutionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantDirectImagePreservesComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantPerfectQuotientProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantScalarDirectImageCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantScalarStrictUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantSquareZeroTorExample | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstantWeilStructureStageIndependence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleHeart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleNormedGeometricFibres | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ContinuousCoefficientFreeRank | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralConstructibleComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralSliceModelComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousPresentationFiberCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ContinuousRepresentationCondensation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoordinateCounitArrows | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DenseLatticeDerivedInvariants | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedExchangeExactNormalization | R3 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedLocalClassEdgeComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.EtaleWeilAbelian | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilFiberHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilRealization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilReconstruction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilRepresentationData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EtaleWeilTensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExceptionalCoefficientComparison | T1 | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExchangeProjectionSuppliedDomains | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExpressionCounitSubstitutionCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FdCommonStageComparisonDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FdIntegralIdentityRationalEquivalence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FdPullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldSeparableCechCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteAffineDirectImageSupportBound | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteClopenConstructibilityBounds | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientIntrinsicChainTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCoefficientTensorCtf | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCompactSupportUniformTor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteComparisonPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteConstantH1Pi1 | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteConstantModelStrataGeneration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteConstantModelsCommonStratification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDirectImageComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDiscreteScalarConstantModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteExpressionReductionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteFieldLisseInternalHom | A5 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteFieldStratifiedPerfectModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteFreeQuotientCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteLevelRectangle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteLineTensorConditions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteLocallyFreeLineModels | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteOpenProductSwap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePerfectAdicMarkedRoos | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePerfectAdicRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePerfectAdicTowerLimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteProperProductTranspose | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePullbackTensorComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FinitePullbackTransitionGenerators | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteReductionExchangeRectangle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteReductionPullbackCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteRegularCoefficientComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteResidueDualizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteRingSectionDeformation | N1 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothCanonicalInterfaces | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteStageKaroubiExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteStagePairCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteStageRationalExchangeData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteTorAmplitudeSites | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FlatCondensedScalarRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FormalClosedPullbackProducts | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FourArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FourierAdicCharacterOf | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FourierSetting | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.FrobeniusFixedPairComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | A5 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.GeometricScalarAssociationCocycle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GeometricStalkPerfect | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.HenselianBoundaryLocalData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndUnipotentProcyclicDifference | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IndUnipotentSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompletedLocalPerfectCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompletedTowerPullbackUniverses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralConstantModelLocalResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleHomSums | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleLinear | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralConstructibleTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralContinuousCokernelLocalModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralContinuousPresentationMatrix | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralCtfTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLfpConstantModelComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralLineDerivedComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLineRestrictions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLocalizationHomColimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralModelsExtensionClosed | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralObjectPullbackLine | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPadicLocalPerfectCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackShiftCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralResidueTor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralScalarExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralScalarExtensionConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralScalarExtensionUniverses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralSectionLocalModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectClosureHomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralStratumChartRestrictions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTStructure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTensorComparisonSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IsomorphismScalarAugmentationCone | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KFlatScalarComparisonNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerBarResolution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerNormalizedComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerResolutionColumns | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerScalarRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.KummerTermMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LevelwiseAdicTruncations | G1 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseLatticeReducedOpen | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseRankOneAut | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalIntegralPerfectModelCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalModelTorBoundDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.LocallyConstantTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | U4 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | B6 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NearbySpreadOut | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NilpotentReductionLissity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NilpotentReductionStep | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.NormAlgclCohomologyTopologyComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedCompletedOperationModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | R4 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedOperationSystemModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedScalarComparisonRealization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.NormalizedTensorConstraintTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormalizedTowerCommonLisseStrata | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.NormedCoefficientRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenComplementUnconditional | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenExtensionFiniteTor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenFiniteConstructibilityInterval | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.OpenImmersionTensorPiece | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenLocalizedCounitComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenRestrictionCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcAutomorphismTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcConstructibleReductionCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcDescentFunctors | J5 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcFiniteDirectImageCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcPairFunctorShiftCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcRationalTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcRectangleDerivedLimit | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PbcScalarExtension | M1 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcUniformLocalModelCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcUniformReductionCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PbcWeilCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerAdicCommonStageTruncations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerfectChartTensorComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerfectLocalReductionModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerfectProjectionFormula | G3 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerfectQuotientExchangeNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PerfectStrataUniformReductions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointAutomorphismRestrictionNatural | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointDerivedSectionsTensorDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointDerivedTensorTowerCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFieldTensorDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFiniteFreeSectionsTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointFiniteTensorComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointIntegralCompletedTensorComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointIntegralPerfectRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointIntegralSectionsConservative | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointQbarFibreShiftDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointRationalFibreExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointRationalSectionsHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointRationalSectionsLattice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointRealizationStandardCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointSectionsScalarExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PreservationConstructible | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PrimeToEllDerivedInvariantsReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PrincipalKoszulRoosReflector | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PrincipalReductionDerivedNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProEtaleConstantReductionModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleConstantReductionTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleScalarMateNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProfiniteCoefficientLinearization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProfiniteConstantDerivedFunctions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProfiniteDerivedEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProfiniteDerivedFunctionsFilteredColimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionFormulaCompactified | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionFormulaIdentityCompactification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionMateSlicePresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PullbackFiniteConstantLocalModel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PullbackTorAmplitude | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PulledReductionComparisonData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PulledReductionNormalizationComparison | E9 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PulledReductionStrictModelDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurEtaleLisseDualizable | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurEtaleLisseStratumCompact | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurLisseMorphismRigidity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityDncFiniteRealization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityFiniteKummerDefinitions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityFiniteSetting | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityKummerNormalizedBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityKummerNormalizedProjection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityKummerRootTensorBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityLisseUniqueness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityNormalCone | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityNormalProjection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityRankOneLocalData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityRegularSection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PuritySupportCommonInjectives | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.PurityVectorBundleZeroSection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QcqsProperSerreHeartBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QuotientDiagramProjectionEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QuotientDiagramScalarProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RamifiedCoefficientQuotientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RamifiedFinitePullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RamifiedPullbackTowerData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RamifiedPullbackTowerIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RankOneClassicalSupportComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RankOneKummerMonomial | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalComparisonDatum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonFunctor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonScalarSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonStageSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonStructures | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonTransition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonTransitionTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalComparisonValid | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalLocallyFree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalOperationCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalRawOperationCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalRawSquareExchangeCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalSquareExchangeCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalStratumIntegralModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalTensorComparisonSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RationalizationIdempotentComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RationalizationKaroubi | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealBoundaryDecompositionLanding | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RealBoundaryLocalConstants | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RealSheafSections | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealWeilSheaves | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationAdjointComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationCoefficientSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationCompletedImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationCompletedPullData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationContinuousDirectImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationLocalizedPush | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationPullOrdinarySystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationPullRationalDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationScalarFunctor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RealizationScalarPushMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ReductionOpenEtaleOrigin | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ReductionPullFiniteEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RefinementBoundaryVanishing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RefinementComparisonComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RefinementComparisonIsomorphism | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RegularQuotientCompletionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RelativeSupportVanishing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ResidueLissePerfectLift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RestrictionLimitProjectionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RingedCoefficientAssociatorShifts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientProjectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientPullbackCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientPullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientPullbackShifts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientScalarShifts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCoefficientScalarUnits | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedCommonQuotientPullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedDerivedSliceLocalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedLocalizationRHomCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedModelCurryingCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedOpenScalarLimitCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedOpenStrictReduction | C1 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedProjectionGlobalModel | unclaimed | New packet module; uses unchanged public data interface. |
| Sheaf.Paper.RingedProjectionLocalModel | unclaimed | New packet module; uses unchanged public data interface. |
| Sheaf.Paper.RingedProjectionRestriction | C2 | Assembly imports unchanged data publicly; proof uses construction lemmas. |
| Sheaf.Paper.RingedProjectionRestrictionData | unclaimed | New packet module; uses unchanged public data interface. |
| Sheaf.Paper.RingedProjectionTensorComparison | unclaimed | New packet module; uses unchanged public data interface. |
| Sheaf.Paper.RingedProjectionTensorShifts | unclaimed | New packet module; uses unchanged public data interface. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedRestrictionLocalIso | unclaimed | New packet module; uses unchanged public data interface. |
| Sheaf.Paper.RingedSitePerfectProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedSliceComparisonsShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedSliceDerivedComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedSliceDerivedMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedSlicePullbackMateNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RingedTopoiDerivedPullbackIndependent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RoosIntrinsicUnitComparison | H6 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootCoordinateSupportedVanishing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootOfUnityModulus | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootTowerCoordinateFace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.RootTowerPunctureInvariance | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarCompletionAssociator | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarExtensionExact | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ScalarPullbackStrictConeNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionCentredChartData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SectionComparisonArrows | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionLocalComparisonData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SectionLocalDualizingComparisons | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionNormalFibreMap | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SectionReesBaseChangeEtale | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearDerivedCalculus | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearDerivedSections | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearGeometryCore | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearGeometryDerived | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearGeometryOps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearOperationsExistence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SemilinearSystemsExistence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SequenceSiteOpenExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | P8 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfCbcDirectImageReductionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfCompleteDirectImageReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfDerivedDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfExceptionalAdjointAdmissibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SfExchanges | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfPreservationClass | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SheafSliceDerivedComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SiteBoundedConstantGradedModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SiteBoundedConstantModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SiteBoundedTruncationModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SiteFiniteFreeTruncationModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SpDirectImageEtaleMate | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SpectralFiniteEtaleTraceLattice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StandingExceptionalBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedDualizableBounded | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedDualizableHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedLatticeScheme | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedPerfectInternalHomCoproducts | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StratumAmbientHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.StratumCompletionUnitRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictPerfectTowerProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictQuotientDiagonalNormalization | C4 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictQuotientExchangeUnitEquation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictQuotientScalarDirectIsomorphisms | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictScalarOrdinaryAdjointsExist | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictScalarOrdinaryAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedCohomologyHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SupportedCup | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SupportedCupFunctoriality | P5 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedHomPullback | B8 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedSectionsHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemCochainTensorReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemNormalizedTensorClosure | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemOrdinaryTensorReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemPushforwardRestrictionTransition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.SystemTensorReductionFormula | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TameBoundaryScalarComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TameInertiaContinuousKoszul | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TensorComparisonLocalizationDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TorsionAcyclicNormCoefficientTest | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TorsionLimitSheafCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TowerPreservation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientSetup | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TrivialLadicDerivedExterior | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.TwoTermReductionCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.UnboundedLocalizingPullback | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.UniformCompleteTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.WContractibleComponentDerivedHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WStrictLisseComponentCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilCompletedTensorReflector | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilInternalHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WeilTensorWeil | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C2 | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.RepresentationTheory.CommonIrreducibilityDetectingCover | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.RepresentationTheory.ProcyclicScalarCochainEvaluation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.LocalizedExtensionZeroLinearDerived | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.OpenBaseChangeDerivedUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.AdmissibleDirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.AdmissibleTensorConstructibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ComparisonOpenTensorCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ConnectedEtalePerfectConstant | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.EtaleStratifiedStalkIdentification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteComparisonsExistence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteCompatibilityTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FiniteOperationComparisons | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | E8 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenOperationModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenPullbackSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenQuotientKoszulCompleteness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenScalarCoefficientCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenScalarProjectionCompatibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenTensorNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenTensorNormalizationData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenTensorSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.OpenTensorSupportAux | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseTowerComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | C7 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SfCategories | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.SmoothPurity.UniqueAdjointCoefficients | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Targets.SliceRestrictionStrictDerivedLimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.Topology.TopologicalModuleCondensation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.CondensedStalkFrobeniusOrbitTrace | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | H7 | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.IsomorphismRoosUnitCancellation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ScalarModelAssociativity | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ScalarModelUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.StrictQuotientCompletionUnit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.StrictQuotientConeAugmentation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Public data re-exported identically; no consumer adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public data re-exported identically; no consumer adaptation. |
| TargetsCheck | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.AlgebraicGeometry.Bertini | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Basic | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Image | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.RankOne | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineInfinityMap | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.CategoryTheory.DerivedCategory.Perfect | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.ConstantExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.FourierTransform.ArtinSchreier | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.GroupTheory.WeilGroup | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Mathlib.GroupTheory.SemidirectProduct | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Mathlib.RingTheory.LaurentSeries | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.RepresentationTheory.Clifford | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.RepresentationTheory.CompositionSeries | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.RepresentationTheory.ExteriorPowerDirectSum | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.RepresentationTheory.FiniteMatrixWitness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.IdentityComponent | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.Coefficients | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | N3 | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.Statement | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Public data re-exported identically; no consumer adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.StalkUpperStar | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.BettiNumbers | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaLinearAlgebra.DetTrace | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaLinearAlgebra.GaloisStrata | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots | unclaimed | Planned DAG consumer; unchanged public data remains available. |
| WeilConjectures.ZetaSeries | unclaimed | Planned DAG consumer; unchanged public data remains available. |

## Status

landed 20261022T023434-L-822000 2026-10-22 (merge of deliver/C2/Sheaf.Paper.RingedProjectionRestriction)

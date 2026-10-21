# CategoryTheory.element_restriction_hom

## Reason

The complete proof uses private projection, Hom-complex, localization and site-equivalence
helpers. Preflight conservatively treats their section, variable, option and local-attribute
commands as an interface effect. This record documents those commands and all source consumers.
No public signature, public import, definition body, global instance or target meaning changes.

## Old

The original public signature was:

```lean
theorem element_restriction_hom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (s : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
        RingedPresentationCore (presentationElementRing R A) (presentationElementRing R B)
          (elementModulePullbackOver.{u, u} (localCoefficientRings R) b
            (presentationElementRestriction_continuous b))),
      (∀ A : Sheaf J (Type u),
        Nonempty (presentationRHom R ⋙
          presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
            (presentationElementRestriction_additive R A)
            (presentationElementRestriction_exact R A).1
            (presentationElementRestriction_exact R A).2.1 ≅
          ((presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1).op.prod
            (presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1)) ⋙
            presentationRHom (presentationElementRing R A))) ∧
      (∀ {A B : Sheaf J (Type u)} (b : B ⟶ A), (s b).unit = Iso.refl _) ∧
      ∀ U : C,
        ∃ E : RingedPresentationEquivalenceCore (R.over U)
          (presentationElementRing R ((presheafToSheaf J (Type u)).obj (yoneda.obj U))),
          Nonempty (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U ⋙
            E.modules.functor ≅ elementModulePullback.{u, u} (localCoefficientRings R)
              ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
```

Its proof was `by sorry`. There were no private helper declarations or their local proof
attributes and section variables in the file.

## New

The public signature remains verbatim:

```lean
theorem element_restriction_hom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (s : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
        RingedPresentationCore (presentationElementRing R A) (presentationElementRing R B)
          (elementModulePullbackOver.{u, u} (localCoefficientRings R) b
            (presentationElementRestriction_continuous b))),
      (∀ A : Sheaf J (Type u),
        Nonempty (presentationRHom R ⋙
          presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
            (presentationElementRestriction_additive R A)
            (presentationElementRestriction_exact R A).1
            (presentationElementRestriction_exact R A).2.1 ≅
          ((presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1).op.prod
            (presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1)) ⋙
            presentationRHom (presentationElementRing R A))) ∧
      (∀ {A B : Sheaf J (Type u)} (b : B ⟶ A), (s b).unit = Iso.refl _) ∧
      ∀ U : C,
        ∃ E : RingedPresentationEquivalenceCore (R.over U)
          (presentationElementRing R ((presheafToSheaf J (Type u)).obj (yoneda.obj U))),
          Nonempty (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U ⋙
            E.modules.functor ≅ elementModulePullback.{u, u} (localCoefficientRings R)
              ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
```

Its proof is complete, with zero local holes. The added helpers are all private and proved.
The added command headers flagged conservatively by preflight are:

```lean
attribute [local irreducible] homComplexFunctor homComplexπ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
section HomComplexComparison
set_option backward.isDefEq.respectTransparency true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
attribute [local irreducible] homComplexDegreeIso
end HomComplexComparison
section DerivedComparison
set_option backward.isDefEq.respectTransparency true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
end DerivedComparison
section ElementHom
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end ElementHom
section IteratedElements
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
end IteratedElements
section RepresentableComparison
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
end RepresentableComparison
```

Section variables are bound in each private declaration, local irreducibility attributes end
with the module, and options control elaboration of this proof. No command registers an exported
instance or simp theorem. Proof-only imports add access to existing comparison APIs; the original
public import of `Sheaf.CategoryTheory.RingedPresentationData` is retained verbatim. All original
public declarations and their visibility are retained. No consumer needs adaptation.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ElementRestrictionHom --uses
CategoryTheory.element_restriction_hom` reports 313 downstream modules and two textual users
(the item and `Sheaf.CategoryTheory.RingedPresentationTransport`). The complete transitive source
consumer list below was also checked independently against both library roots. Claim holders
were read when this record was prepared. All consumers are unaffected by the private proof commands.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.KunnethSupported | P9 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.ElementRestrictionHom | E2 | Original public theorem proved; signature retained verbatim. |
| Sheaf.CategoryTheory.RingedEquivalenceLocalTests | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.RingedPresentationTransport | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation | A3 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CommonStageCalculus | B8 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CommonStageLisse | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompleteProetale | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | M3 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedCoefficientPullbackLinearity | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedDirectImageLimits | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedKoszulQuotientComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedLineTensorCoherence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedPullback | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedPullbackReduction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedPullbackUnitTower | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedReductionPullbackSquare | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ConstantDerivedLimitResolutionUnit | U5 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.DerivedFiniteQuotientCoherence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.EtaleIsoDescent | R5 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FdPullbackComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FinitePullbackTensorComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FiniteReductionExchangeRectangle | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FourArrows | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.GeometricStalkPerfect | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IntegralCtfTriangulated | F6 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.NearbySpreadOut | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | S4 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcDescentFunctors | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcPairFunctorShiftCoherence | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcQbarCompletedPullback | M2 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcScalarExtension | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointAutomorphismRestrictionNatural | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | Q9 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointFibreEquivalence | B5 | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ProEtaleConstantReductionModels | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ProEtaleConstantReductionTower | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.RealSheafSections | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.RealWeilSheaves | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.RingedSitePerfectProjectionFormula | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfCbcDirectImageReductionUnit | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfExchanges | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.StratumCompletionUnitRestriction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.UniformCompleteTensor | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.WeilInternalHom | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Paper.WeilTensorWeil | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No adaptation: signature, public imports and exported instances unchanged. |

## Status

landed 20261021T120342-L-3819623 2026-10-21 (merge of deliver/E2/Sheaf.CategoryTheory.ElementRestrictionHom)

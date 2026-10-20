# AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek

## Reason

Fill the assigned proof without changing the arbitrary-ring statement. The private helper
extends the unit projection formula to every constant module by generation and coproduct
preservation. The main proof uses the proper/open factorization of the compactification.

Preflight conservatively flags the added command `omit [HasCompactification f] in` as a
surrounding-command change. Its effect is confined to the following private theorem; it does
not change the existing section variables or any existing declaration. This record documents
that scope. The only edited module is the item, held by D8.

## Old

The existing public signature, verbatim (its proof was `sorry`):

```lean
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ])
```

There was no private `constant_projection_of_preservesCoproducts` helper and no scoped `omit`
command at this point.

## New

The public signature remains verbatim:

```lean
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ])
```

Its proof is complete from existing library statements. Immediately before it is a completely
proved private helper, scoped by `omit [HasCompactification f] in`, which asserts invertibility
of the projection comparison at any constant coefficient module whenever derived direct image
preserves coproducts. The scoped command drops an irrelevant assumption about the unrelated
morphism `f` from this private helper only.

Two proof-only imports are added under `WeilConjectures.SixFunctors.Etale.Derived`:
`ConstantTensorProjection` and `CompactificationUpperShriek`. Existing signatures, attributes,
public imports, docstrings, and non-theorem bodies are unchanged.

The proof uses the current original source instance
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`,
which still has its original `sorry`. This delivery does not settle that stronger assertion's
geometric scope. The assigned theorem's existing disputed-scope comments remain.

## Users

The following table includes the 394 downstream modules identified by `tools/downstream.py`
and the edited item. No executable use of the assigned declaration was found outside its own
module. All consumer signatures and definitions stay unchanged; no consumer is adapted.
Holders below are read from current project claims, with no claim meaning unclaimed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.ComparisonTorInterval | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackBase | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedSupportTriangle | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SupportedExteriorProduct | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.AlgebraicGeometry.SupportedProductQuotientModel | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.BoundaryExceptionalComparisonData | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.CohomologicalSmoothnessComparison | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.CohomologicalSmoothnessFiniteComparison | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.ConnectedTateLineEndomorphisms | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.DirectImageTorAmplitude | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.FiniteFieldSheafScalarExtension | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.FiniteRingCompactSupportProjectionMap | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.FiniteRingConstructibleDerivedOrigin | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.OpenComplementUnconditional | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PullbackTorAmplitude | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PurityAffineChartBounds | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PurityDncFamily | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PurityDncFiniteRealization | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PuritySectionInvariant | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.PuritySectionInvariantCompared | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.SfDirectImageCTFNonproper | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.SfPreservationClass | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.SpDirectImageEtaleMate | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.Paper.WeilVerdierPreservationStrata | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SixFunctors.AdmissibleDirectImage | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SixFunctors.ExceptionalBaseChangeAffineLocality | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SixFunctors.ExceptionalBaseChangeOpenRestriction | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.SixFunctors.SmoothDualityBaseChangeCompat | unclaimed | No API change; no executable use; unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No API change; no executable use; unchanged. |
| TargetsCheck | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineGluing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineKunneth | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologyHom | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerGenerator | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerRelative | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerRelativeBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.OrientationGeometricPoint | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RankOneLocal | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariant | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedCup | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.EtaleCohomology.TateTwist.Preserves | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Composition | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperAdicLattice | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperAdicTower | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicSystem | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Admissibility | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundedConstructibleUpperShriek | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClopenTransfer | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionPositiveDegree | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportAmplitude | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportAssembly | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTorAmplitude | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportCoefficientChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationRestrict | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | D8 | Proof completed; private helper and proof imports added. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CurveOpenDirectImage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GeometricStalk | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.OpenComplement | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralConstructible | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.InvertibleLocal | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointBiduality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberAlgClosed | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberRational | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PurityPreservation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChangeCharts | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Charts | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.OpenImmersion | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChangeUnit | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekDualBaseChange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.AffineDirectImage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.AffinePushforward | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarMittagLeffler | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLimit | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLisse | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeModule | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimit | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimitTStructure | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsConstructible | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchangeComparison | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.GeometricStalk | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizingLowerShriek | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.SmoothProperLocallyConstant | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.Statement | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FieldCoefficientForget | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FieldCoefficientKaroubian | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FieldCoefficientTransition | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FieldCoefficientTriangulated | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No API change; no executable use; unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No API change; no executable use; unchanged. |

## Status

landed 20261020T151214-L-2646820 2026-10-20 (merge of deliver/D8/WeilConjectures.SixFunctors.Etale.Derived.Exchange)

The final Lean file compiled cleanly via `lcompile.py` in 42.0 seconds. The delivery check
requested this record for the scoped private-helper command. There is no public interface
change or forced adaptation. Independent review remains responsible for the disclosed use
of the stronger existing admitted instance.

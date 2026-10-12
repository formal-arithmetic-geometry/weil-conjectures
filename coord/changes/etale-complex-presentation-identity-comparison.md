# AlgebraicGeometry.Etale.ComplexPullbackPresentation.hidentity

## Reason
The profiler reports 26.7 seconds checking this projection, repeatedly unfolding inverse-image
functors to identify the codomain of the equality transport. The original complete assembly
exceeded the 60-second limit. A concrete named comparison with an explicit source and target
eliminates this unfolding for the field and its users. The helper is a transparent definition,
not an axiom or a postponed proof. The field remains definitionally equal to its old form.
No target statement or mathematical definition changes meaning, and no target review reopens.

## Old
```lean
  hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i)
```
The parent had proof imports of ExactFunctor, Derived.LowerShriek and UpperLowerStar.Defs.

## New
```lean
  hidentity : ∀ i : I, φ (𝟙 i) = presentationIdentityMap D i (F i)
```
The body of `presentationIdentityMap` is exactly the old right-hand side with `C` for `F i`.
The parent publicly imports EtaleComplexPullbackTransport because its field now names the
helper. Coherence remains a proof import. The three redundant original proof imports are removed.
The nonempty theorem's signature is unchanged, including all binders and hypotheses.

## Users
`tools/downstream.py ... --uses AlgebraicGeometry.Etale.ComplexPullbackPresentation` lists
170 downstream modules. Its textual name search finds only the defining module, but the
projection caller DerivedEtaleCohomologyLimit was also inspected and compiled (38.9 seconds).
The table records every downstream module. All statements keep exactly their original meaning;
other modules do not require edits. Claim holders are read from this machine's snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleComplexPullbackPresentation | C2 | Identity law now uses the named, explicitly typed comparison. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | T1 | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unclaimed | Uses v.hidentity; unchanged source compiled against the repaired presentation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts | M2 | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | F2 | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unclaimed | Definitionally identical field; no source adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Definitionally identical field; no source adaptation required. |
| TargetsCheck | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | A2 | Definitionally identical field; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | C1 | Definitionally identical field; no source adaptation required. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Gabber | S2 | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Definitionally identical field; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Definitionally identical field; no source adaptation required. |

## Status
landed 20261012T095854-L-313161 2026-10-12 (merge of deliver/C2/Sheaf.AlgebraicGeometry.EtaleComplexPullbackPresentation)

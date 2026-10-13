# AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_restriction

## Reason

Repair reviewer X-4d817, head 4d817af8f, H3 / brief point 6. The DAG prose
claimed arbitrary derived coefficients, whereas its Lean record has always stated
the over-W specialization with canonical coefficients. Correct the prose to match
that existing signature and the delivered specialization proof. This records an
intermediate DAG statement correction under stage 3 section 3; no Lean signature,
visibility, definition, target statement or mathematical meaning of a target changes.
The general result remains in sbc-lem-higher-image-raw-triangle-restriction.

## Old

For a commutative ring Λ, schemes Y, Y′, S, morphisms a:Y′→Y, h:Y→S, h′:Y′→S with a≫h=h′, bounded-below derived module sheaves K on Y and K′ on Y′, integer q, and a specified derived coefficient morphism v:a* K→K′ [def-weil-pbc-derived-categories], [def-weil-pbc-etale-sheaves], define r_U(z) by the single-complex map of the pullback composition isomorphism, the inverse single-complex comparison, derived pullback of z, the shift comparison, and v[q] [lem-weil-pbc-inverse-image-composition]. For etale S-objects T,U, b:T→U and a raw class z∈Hom(h*Λ[U][0],K[q]), one has r_T(z|_T)=r_U(z)|_T.

## New

For a commutative ring Λ, schemes W and S, k:W→S, a sheaf G of Λ-modules on W_et, an integer q, objects A and B over W, and f:A→B over W, put K_B=(B^*G)[0] and K_A=(A^*G)[0] [def-weil-pbc-derived-categories], [def-weil-pbc-etale-sheaves]. For an etale S-object U, put P_B(U)=Hom(((B→S)^*Λ[U])[0],K_B[q]), and likewise P_A [def-weil-pbc-direct-image]. Define r_f:P_B(U)→P_A(U) by pullback composition, the inverse single-complex comparison, derived pullback of the class, the shift comparison, and the shifted canonical coefficient identification f^*K_B→K_A [lem-weil-pbc-inverse-image-composition]. For etale S-objects T,U, b:T→U and z∈P_B(U), one has r_f(z|_T)=r_f(z)|_T.

## Users

The downstream scan for this module and `--uses higherDirectImageRawOverPullback_restriction`
finds only the item itself as a textual declaration user. The table covers all transitive
importers, as in the existing factorization change record; no module needs adaptation.
No base DAG node cites the restriction node in stmt_deps or proof_deps, so
statement_change.citers is empty. The conjunction node acquires that dependency in this
delivery and uses exactly the corrected specialization; its conclusion stays unchanged.


The factorization record inventories 202 transitive downstream modules and seven
textual users of the pullback definition (including the item). The table below
covers the same transitive importers for this prose correction. It introduces no
Lean definition change; the separate factorization is recorded in
higherDirectImageRawOverPullback-factor-triangle.md. No external module is adapted.
For untouched modules the holder column says `not adapted` when no local claim
record is available; no adaptation depends on a claim exception.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | V1 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation | C2 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | V1 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackComposition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula | U2 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity | M4 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | N1 | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| TargetsCheck | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted | Prose correction only; Lean signatures, definitions and uses unchanged; no adaptation. |

## Status

landed 20261013T100155-L-2495270 2026-10-13 (merge of deliver/V1/Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality)

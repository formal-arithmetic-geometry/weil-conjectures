# AlgebraicGeometry.ProEtale.scalarExtensionFunctor proof context

## Reason

The repair removes the inherited warning-suppression option, so the source hole
census no longer mistakes its name for an unattributed hole. Lean warnings remain
enabled; removing this option changes no declaration or proof.
The private `scalarExtension_cochainModelIso` is now a proved `Nonempty` theorem,
rather than a data-valued definition. Its sole consumer obtains the isomorphism
locally; this avoids unfolding its universal-derived construction in the transport
proof. This performance repair changes no public declaration.

Stage-3 preflight requests a change record for the added proof-context commands
in `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`. They support proofs of the 15
existing theorems: size-correct sheafification, the native bounded flat model,
ordinary scalar extension, signed Tate tensors and duals, and derived coherence.
Every original public signature, all 14 original definition bodies and every public
import are verbatim unchanged. No adopted source-library module is edited.

The three smallness helpers are private theorems registered using explicitly
local instance attributes. The standard derived-category instance and the
irreducibility attributes are also local. `open` commands and transparency options
control elaboration inside this file. Disabling the unsuitable fixed-coefficient
instances avoids unconstrained universe maxima. The helper statements are proved;
no new public API, axiom, theorem hole or hollow definition is introduced.

## Old

The public scalar functor signature and body, verbatim:

```lean
noncomputable def scalarExtensionFunctor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  scalarExtension f T
```

The added proof-context sections and private smallness helpers did not exist.
The 15 theorem bodies were `by sorry`.

## New

The public scalar functor signature and body, verbatim unchanged:

```lean
noncomputable def scalarExtensionFunctor {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  scalarExtension f T
```

The three private smallness helpers all have the following type and proof (with
names `scalarExtensionSmall`, `scalarTateSmall`, and `scalarTateExponentSmall`):

```lean
private theorem scalarExtensionSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] scalarExtensionSmall
```

Other proof-context commands include:

```lean
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] scalarExtensionTateMaps scalarExtensionTateLevelIso
attribute [local irreducible] scalarExtensionFunctor_composition
attribute [local irreducible] scalarExtension_composite
attribute [local irreducible] scalarExtension_positiveComparison
attribute [local irreducible] scalarExtensionFunctorCounit
  completedAdicChangeData
```

Private normalization lemmas for the chosen Tate maps, level maps and derived
composition supply their defining formulas without unfolding the choices.
The identity-extension formula is converted once to the native interface and reused.
Stricter transparency is scoped to the exponent and final coherence proofs,
with the original transparency restored where concrete category aliases must be
identified. The full proof uses private imports and fully proved private helpers. In particular,
the tensor/Tor comparison is first proved for an abstract monoidal Grothendieck
abelian category and then specialized, preventing costly repeated unfolding of the
sheafification construction. These changes do not alter the meanings of any target,
so no statement review is reopened. All 15 original theorem statements are proved.

## Users

`tools/downstream.py Sheaf.SecSmoothPurity.ScalarExtensionFunctor --names` lists
370 transitive consumers in the current checkout. Their public imports and
interfaces remain available unchanged. None requires adaptation; no consumer is
edited. Claim holders below are from the current claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | A2 | Assigned proofs completed; public interface unchanged. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | B2 | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RealWeights | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Interface unchanged; no adaptation required. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SmoothTrace | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TwConventions | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WfTateTwist | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Interface unchanged; no adaptation required. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Interface unchanged; no adaptation required. |

## Status

landed 20261022T013341-L-3548851 2026-10-22 (merge of deliver/A2/Sheaf.SecSmoothPurity.ScalarExtensionFunctor)

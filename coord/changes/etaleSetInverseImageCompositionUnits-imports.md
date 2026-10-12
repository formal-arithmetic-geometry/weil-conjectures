# etaleSetInverseImageCompositionUnits imports

## Reason

The set-valued composition theorem uses only the existing set-pullback definition and
adjunctions. The algebraic-structure-lifting theorem and local-section theorem are
unnecessary. Replace the public import by the narrower defining modules, and add only
proof imports for the coefficient-independent coherence calculation. No definition,
public declaration signature, universe or target statement changes. This record is
required by the preflight for removal of a public import. The proof-dependency pruning
is recorded in the existing DAG node and in report.md.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.Paper.SiteSheafificationSectionsLocal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
--uses etaleSetInverseImageCompositionUnits` lists the following downstream modules.
The theorem's unchanged statement and definitions keep every use identical. The removed
modules provide no definition used by the statement; the exact definitions and continuity
instance modules are now imported publicly. All helper declarations are private and proved.
No downstream module is modified or needs a mathematical statement review. Claim holders
below are the read-only local claim snapshot; no other group's work is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits | R1 | Proof completed; statement unchanged |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | F1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison | C1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | S1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection | T1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelection | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | Q1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | J2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | S2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | V1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | G1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | P1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | U2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | U2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion | T2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections | ORCHESTRA | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | ORCHESTRA | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | ORCHESTRA | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction | S1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity | T1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres | ORCHESTRA | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | D2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.GmPicardPullback | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.IrreducibleLisseStrata | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | Q1 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | ORCHESTRA | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | V2 | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension | unclaimed | No statement or definition changes; no adaptation required |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement or definition changes; no adaptation required |
| TargetsCheck | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | H1 | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | Q2 | No statement or definition changes; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | T1 | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | F1 | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | X2 | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement or definition changes; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement or definition changes; no adaptation required |

The direct textual users of the theorem are EtaleGeometricFibreConstantSections,
EtaleGeometricFibreInverseImageConstant, EtaleSectionsFpqcDescent, EtaleSetSectionContinuity,
and FiniteSurjectiveSetDescent; each uses the same theorem statement after this change.
The import-pruning checker is also run on the original and new files to check for lost
transitive declarations. Final downstream compilation remains the maintainer's global build.

## Status

landed 20261012T044752-L-2038986 2026-10-12 (merge of deliver/R1/Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits)

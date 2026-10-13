# AlgebraicGeometry.Scheme.Modules.affine_module_finite_type

## Reason

The conservative interface checker reports added helper sections, universe and
variable commands, local opens, and local notation as a command change. They scope
proved private proof helpers; no existing public declaration, visibility, instance,
attribute, definition, or public import changes. This record documents the lexical
changes for the independent reader. No importer needs adaptation and no target's
meaning changes.

## Old

The original file has `universe u`, `open CategoryTheory TopologicalSpace`, the
namespace `AlgebraicGeometry.Scheme.Modules`, `noncomputable section`, the two
transparency options, and these variables and local notations:

```lean
variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "AR" => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)
```

The public declaration is:

```lean
theorem affine_module_finite_type [IsAffineHom f]
    (M : SheafOfModules.{u} AR) (hM : M.IsQuasicoherent)
    (F : U.Modules) (hF : F.IsQuasicoherent) (e : (R).obj F ≅ M) :
    M.IsFiniteType ↔ F.IsFiniteType
```

## New

The public declaration above is identical. Its statement's `R` notation expands
to the same functor. Added `section SiteHelpers` introduces `universe v w`, opens
`SheafOfModules CategoryTheory.Limits`, and variables for three proved private
helpers on a general site. That section ends before the affine cover helper.
A private affine cover helper and private finite-generator helper are also added.
The latter has a local documented `maxHeartbeats` setting. All helpers are proved.

Before the finite-generator helper, the old pushforward notation is called PUSH
to avoid capture of the named parameter `R :=` in free-module expressions. Before
the existing public theorem the original name is restored by:

```lean
set_option hygiene false in
local notation "PUSH" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)

-- The proved private finite-generator helper occurs here.

set_option hygiene false in
local notation "R" => PUSH
```

These are local notations. No command adds a global instance, elaboration
attribute, or notation. Existing signatures and their elaborated meaning remain
identical; no definition used by a target changes.

## Users

All transitive importers from `tools/downstream.py` are listed below. The two
modules mentioning `affine_module_finite_type` are the item itself and
`Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange`. In all cases the original
public theorem type and public imports stay identical, so original modules compile
without any forced adaptation. The holder column records the local claim snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData | B2 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCore | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreCandidate | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GradedSerreVanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjectivePullback | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VanishingProjective | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | E3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Public interface unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineModuleFiniteType | E4 | Public interface unchanged; no adaptation. |

## Status

landed 20261013T054213-L-441846 2026-10-13 (merge of deliver/E4/Sheaf.AlgebraicGeometry.AffineModuleFiniteType)

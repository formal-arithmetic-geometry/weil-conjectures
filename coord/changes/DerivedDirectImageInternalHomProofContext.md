# DerivedDirectImageInternalHomProofContext

## Reason

The static command comparison requires this record for new module-local options,
universe names, and section variables used by the proved private generic helpers.
These are proof context, and do not change the existing public theorem or anything
an importing module resolves. Section variables end before the original theorem.
There are no new instances, attributes, notation, public declarations, or public imports.
No definition used by a target has changed; no target statement review is reopened.
All 330 downstream modules are listed below conservatively; none requires adaptation.
The --uses search finds no downstream textual use of the theorem, only its declaration.

## Old

Module commands (comments and whitespace normalized by the project's parser):

```lean
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

public import Sheaf.Algebra.Homology.DerivedInternalHom

public import Sheaf.AlgebraicGeometry.DerivedPullback

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction

import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct

import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
```

The original public signature is:

```lean
theorem exists_derivedDirectImage_internalHom_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
      (bX : ∀ L : schemeDerivedCategory X, tensorRight L ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)).obj
            (op L))
      (bY : ∀ L : schemeDerivedCategory Y, tensorRight L ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
            (op L))
      (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
        (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
      (c : derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf ⋙
          schemeDerivedDirectImage f ⟶
        (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
          derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf),
      ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
        (α : A ⟶ (schemeDerivedDirectImage f).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).obj
            (op L, M))),
        ((bY ((schemeDerivedDirectImage f).obj L)).homEquiv A
          ((schemeDerivedDirectImage f).obj M)).symm (α ≫ c.app (op L, M)) =
        a.homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
          (t.hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
            (𝟙 ((derivedPullback f).obj A) ⊗ₘ a.counit.app L) ≫
            ((bX L).homEquiv ((derivedPullback f).obj A) M).symm
              ((a.homEquiv A
                ((derivedInternalHom (Opens.grothendieckTopology X)
                  X.toRingedSpace.sheaf).obj (op L, M))).symm α))
```

## New

Module commands (same normalization):

```lean
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

public import Sheaf.Algebra.Homology.DerivedInternalHom

public import Sheaf.AlgebraicGeometry.DerivedPullback

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel

import Sheaf.AlgebraicGeometry.DerivedAdjoint

import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxSize 2048

universe u w vC vD uC uD

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [MonoidalCategory C] [MonoidalCategory D]

variable (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D) (F : D ⥤ C) (R : C ⥤ D) (p : F ⊣ R) (t : tensor D ⋙ F ⟶ F.prod F ⋙ tensor C) (ex : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M)) (ey : ∀ A L M : D, (A ⟶ J.obj (op L, M)) ≃ (A ⊗ L ⟶ M)) (hx : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M') (g : A ⟶ H.obj (op L, M)), ex A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ ex A L M g ≫ d) (hy : ∀ (A A' L L' M M' : D) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M') (g : A ⟶ J.obj (op L, M)), ey A' L' M' (a ≫ g ≫ J.map (b.op, d)) = (a ⊗ₘ b) ≫ ey A L M g ≫ d)

include hx hy in

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C) (e : ∀ A L M : C, (A ⟶ H.obj (op L, M)) ≃ (A ⊗ L ⟶ M)) (h : ∀ (A A' L L' M M' : C) (a : A' ⟶ A) (b : L' ⟶ L) (d : M ⟶ M') (g : A ⟶ H.obj (op L, M)), e A' L' M' (a ≫ g ≫ H.map (b.op, d)) = (a ⊗ₘ b) ≫ e A L M g ≫ d)
```

The public signature is verbatim the Old signature above. The only declarations
added are the proved private internalHomMate_of_tensorComparison and tensorAdjunctionCore.
No existing definition, signature or visibility changed. All three added imports
are ordinary proof imports. The original four public imports remain identical.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | T3 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | X3 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | K2 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | V1 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | E2 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| TargetsCheck | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature, definition, instance or visibility change; no adaptation required. |

## Status

landed 20261013T062537-L-737388 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom)

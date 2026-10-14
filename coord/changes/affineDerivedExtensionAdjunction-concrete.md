# affineDerivedExtensionAdjunction

## Reason

The second reader found that the earlier delivery changed only a comment and
incorrectly claimed the repair was complete. The old existential theorem fixes no
adjunction Hom equivalence: on a fixed functor one can twist it by minus one.
Construct the scalar-extension functor from the source-library K-flat construction
and descend Mathlib's specified extendRestrictScalarsAdj using its fixed derived
counit/unit. Exact scalar restriction is transported by its unit-compatible
rightDerivedFunctorIsoMapDerivedCategory. The preservation proof is extracted to
the proved named theorem ModuleCat.extendScalars_preservesKFlatQuasiIso; the
existing existence theorem keeps its signature and now follows from the construction.
This is a partial repair: canonicalPullbackAdjunction still needs the original
shared derivedPullback counit, together with the shared composition and model APIs.

The public declaration signatures remain verbatim. The selected scalar functor
and adjunction data change, so every target using these definitions transitively
needs its semantic review reopened under AGENTS.md section 4. The canonical
normalization is the intended scalar-extension map; no target statement is edited.
The new public imports support exposed definition bodies. The mixed-tensor proof
import moves to the property module and is no longer a direct import of the item.

## Old

```lean
def affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  Classical.choose (exists_affineDerivedExtension g)
```

```lean
def affineDerivedExtensionAdjunction {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    affineDerivedExtension g ⊣
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory :=
  Classical.choice (Classical.choose_spec (exists_affineDerivedExtension g))
```

## New

```lean
def affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B) := by
  -- Retain the original sheaf-derived-category parameter in the exposed API.
  let _ := ‹∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))›
  let ρ := affineBaseRingMap g
  have : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} ρ).PreservesKFlatQuasiIso :=
    ModuleCat.extendScalars_preservesKFlatQuasiIso ρ
  exact (ModuleCat.extendScalars.{u, u, u} ρ).leftDerivedFunctor
```

```lean
def affineDerivedExtensionAdjunction {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    affineDerivedExtension g ⊣
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory := by
  let ρ := affineBaseRingMap g
  have : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} ρ).PreservesKFlatQuasiIso :=
    ModuleCat.extendScalars_preservesKFlatQuasiIso ρ
  exact (ModuleCat.extendRestrictScalarsAdj ρ).derivedAdjunction.ofNatIsoRight
    (ModuleCat.restrictScalars.{u} ρ).rightDerivedFunctorIsoMapDerivedCategory
```

## Users

Source inspection used tools/downstream.py and searches for both changed names.
All direct users use the generic adjunction laws or a comparison by
Adjunction.leftAdjointUniq, and none unfolds the old existential witness.
Their statements still assert the same functor-invariant facts and normalized
unit/mate equations. No mathematical proof adaptation is required by source inspection.
Other transitive users keep their textual signatures; target semantic review
must account for the corrected scalar normalization. Rows below enumerate the
full downstream import closure at this review, including modules not mentioning
either name. AffineSectionsSquareComparisonCoherence is also delivered with only
the theorem-local heartbeat adjustment recorded in its row below; the independent
reading checks the original against the changed dependencies.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineExtensionModelUnit | unclaimed | Generic adjunction/uniqueness argument; signature preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelFactorization | unclaimed | Generic adjunction/uniqueness argument; signature preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate | unclaimed | Generic adjunction/uniqueness argument; signature preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnderivedModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit | unclaimed | Generic adjunction/uniqueness argument; signature preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Generic adjunction/uniqueness argument; signature preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsUnitUncancelled | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | unclaimed | Generic adjunction/uniqueness argument; signature preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineSectionsCompositionComparisons | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence | unclaimed | Forced adaptation: theorem-local maxHeartbeats 800000 before its docstring fixes the reviewer-reported elaboration timeout; signature and body preserved; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | N2 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback | B2 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenRestriction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenUnit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedOpenRestrictionUnitIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | C3 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisColumns | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData | H1 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | E2 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | H1 | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_three | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_zero | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVConePresentation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVExactOpenComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenComparisons | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVOpenCoefficientTransport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedVertexComparisons | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMVSESPresentation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| TargetsCheck | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer; signature preserved; no adaptation; review normalized target meaning. |

## Status

landed 20261014T030648-L-344778 2026-10-14 (merge of deliver/S3/Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap)

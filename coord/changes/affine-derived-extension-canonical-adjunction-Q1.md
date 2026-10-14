# AlgebraicGeometry.affineDerivedExtensionAdjunction

## Reason

The existing definition chooses unrestricted left-adjoint and adjunction witnesses.
An adjunction twist changes the literal base-change map. Construct affineDerivedExtension
from extendScalars.leftDerivedFunctor with its specified K-flat counit; derive Mathlib's
extendRestrictScalarsAdj and transport exact restriction through the unit-compatible
rightDerivedFunctorIsoMapDerivedCategory. No independently chosen scalar data remains.

S3's earlier repair was briefly present when this reading started, but the global build
reverted it after an importer universe error. This delivery reuses the existing private
scalarExtension_quasiIso_of_kFlat proof through a proved public preservation wrapper,
rather than adding a CommRingCat-specific duplicate of that proof to the item.

All existing signatures and instance parameters stay identical. The object and adjunction
data used in target meanings change, so semantic review of every affected target reopens
under AGENTS.md section 4. No target text changes. The canonicalPullbackAdjunction issue
remains explicitly open and is not changed in this partial repair.

## Old

```lean
set_option linter.unusedSectionVars false in
-- Preserve the original derived-category instances in the theorem signature.
/-- Derived extension of scalars, chosen from its adjunction with restriction
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map).
Proof: resolve complexes of R-modules by K-flat complexes and apply the existing
ModuleCat.extendScalars termwise. Extension preserves quasi-isomorphisms between
K-flat resolutions. The extension/restriction adjunction on complexes descends to
localizations: restriction is exact, and K-flat resolutions compute the left derived
extension. Thus derived extension is left adjoint to exact derived restriction. -/
theorem exists_affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    ∃ E : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B),
      Nonempty (E ⊣ (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory) := by
  let ρ := affineBaseRingMap g
  have : (ModuleCat.extendScalars.{u, u, u} ρ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} ρ).PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ α hα
    let N := (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj (𝟙_ _)
    have h := (CochainComplex.mixedTensor_kFlat_quasiIso ρ).1 N P Q α hα hP hQ
    let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor ρ).flip (𝟙_ (ModuleCat.{u} B))
    have h' : QuasiIso
        ((((ModuleCat.mixedTensor ρ).obj (𝟙_ (ModuleCat.{u} B))).mapHomologicalComplex
          (.up ℤ)).map α) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality α).symm)).1 h
    let e₀ : (ModuleCat.mixedTensor ρ).obj (𝟙_ (ModuleCat.{u} B)) ≅
        ModuleCat.extendScalars.{u, u, u} ρ :=
      Functor.isoWhiskerLeft (ModuleCat.extendScalars ρ)
        (leftUnitorNatIso (ModuleCat.{u} B)) ≪≫ Functor.rightUnitor _
    let e₁ := NatIso.mapHomologicalComplex e₀ (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e₁.app P) (e₁.app Q) (e₁.hom.naturality α).symm)).1 h'
  refine ⟨(ModuleCat.extendScalars.{u, u, u} ρ).leftDerivedFunctor, ⟨?_⟩⟩
  exact (ModuleCat.extendRestrictScalarsAdj ρ).derivedAdjunction.ofNatIsoRight
    (ModuleCat.restrictScalars.{u} ρ).rightDerivedFunctorIsoMapDerivedCategory

/-- Derived tensor with B, chosen as the left adjoint of exact restriction.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  Classical.choose (exists_affineDerivedExtension g)

/-- The derived extension/restriction adjunction.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineDerivedExtensionAdjunction {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    affineDerivedExtension g ⊣
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory :=
  Classical.choice (Classical.choose_spec (exists_affineDerivedExtension g))

```

## New

```lean
/-- Derived extension of scalars, constructed with the fixed K-flat derived counit.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
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

/-- The specified extension/restriction adjunction descended from
ModuleCat.extendRestrictScalarsAdj, with the fixed left-derived counit and
right-derived unit. Exact restriction is identified with its derived functor
by the unit-compatible comparison, so no independent adjunction witness is chosen.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
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

set_option linter.unusedSectionVars false in
-- Preserve the original derived-category instances in the theorem signature.
/-- Derived extension of scalars, chosen from its adjunction with restriction
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map).
Proof: resolve complexes of R-modules by K-flat complexes and apply the existing
ModuleCat.extendScalars termwise. Extension preserves quasi-isomorphisms between
K-flat resolutions. The extension/restriction adjunction on complexes descends to
localizations: restriction is exact, and K-flat resolutions compute the left derived
extension. Thus derived extension is left adjoint to exact derived restriction. -/
theorem exists_affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    ∃ E : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B),
      Nonempty (E ⊣ (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory) := by
  exact ⟨affineDerivedExtension g, ⟨affineDerivedExtensionAdjunction g⟩⟩

-- Keep the concrete scalar-derived resolution machinery out of unrelated proof search.
attribute [local irreducible] affineDerivedExtension affineDerivedExtensionAdjunction

```

The new ExtensionKFlatQuasiIso module declares the proved preservation property.
Its import must be public because the theorem appears in the exposed scalar definitions:
Lean rejects a private import there. DerivedCategory.Adjunction and FlatResolution also
remain public for exposed construction data. The preservation wrapper's private proof
import avoids re-exporting KFlatScalarExtensionDerivedIso's unrelated proof machinery.
Three redundant direct imports are removed; their public paths remain through the
retained Adjunction, CanonicalDerivedTensorHom and GlobalDerivedHom modules.

## Users

Source inspection listed 504 downstream modules. The group-holder entries were recorded
at the first reading, where available. These declarations use the adjunction abstractly;
the reported failed importer is checked explicitly against the delivered overlay. Any
forced adaptation is listed separately in the report and below. All target semantic
reviews affected by the changed data reopen, even for transitive importers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineExtensionModelUnit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelFactorization | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnderivedModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsUnitUncancelled | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineSectionsCompositionComparisons | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence | unclaimed | Forced adaptation: theorem-local maxHeartbeats 800000 with explanatory comment; original deterministic timeout against overlay, adapted compiles. Signature and proof body unchanged. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | H1 | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | Y3 | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenRestriction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenTranspose | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenUnit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedOpenRestrictionUnitIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | V2 | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisColumns | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedEquiv | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedMaps | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | H1 | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_three | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_zero | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | U4 | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Forced adaptation: overFunctor.{u} in the local hP proof; original fails against overlay, adapted compiles. No signature change. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVConePresentation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVExactOpenComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenComparisons | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVOpenCoefficientTransport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedVertexComparisons | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMVSESPresentation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| TargetsCheck | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same signatures; fixed scalar adjunction; no source adaptation unless separately recorded. Target semantic review reopens. |

The forced importer adaptation is exactly:

```lean
-- Old local proof term:
(SheafOfModules.overFunctor (moduleRings Y.toRingedSpace) U).mapDerivedCategory.mapIso
-- New local proof term:
(SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).mapDerivedCategory.mapIso
```

It supplies the already intended module universe, avoiding a new imported instance's
inference of u+1. Baseline original, overlay original, and overlay adapted were compiled
independently; their results are in the report's Forced adaptations section. No other
line of this unheld module changes.

A second forced adaptation is in the unclaimed
Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence. Its original compiles
against the baseline but reaches the 200000-heartbeat limit when elaborating its signature
against the changed public construction imports. Add only these lines before the original
theorem docstring:

```lean
set_option maxHeartbeats 800000 in
-- The exposed derived-scalar construction increases signature elaboration work.
```

The original theorem signature and proof body remain byte-identical. The adapted file
compiles within 60 seconds. This adjustment changes no logical data or hypothesis.

## Status

landed 20261014T035545-L-887788 2026-10-14 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap)

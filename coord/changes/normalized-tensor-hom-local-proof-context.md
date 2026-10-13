# AlgebraicGeometry.normalizedTensorHomCochains_component

## Reason

The dry-run preflight requires a change record because the proof adds scoped commands
(`variable`, local notation, local attributes and sections). This record documents that
these commands introduce a private proof context; the existing public declaration and
its type are identical. No existing definition is changed, including
`homTensorCurrySectionMap`. The irreducibility attributes are local to this file and
explicit `unfold` opens the section map at the adjunction calculation. All ten new
helper theorems are private and proved. The uncurrying helper rewrites with
`SheafOfModules.tensorHomEquiv_val` before changing its type, keeping the equivalence
locally irreducible and avoiding its repeated expansion. The extensionality helper rewrites
`SheafOfModules.comp_val` with `rw` after explicitly unfolding the section map,
rather than asking an elaborating rewrite to unfold further definitions. There are no public additions, forced adaptations,
or changes to a Challenge target or a definition it uses.

The further H10 repair (returned head 38e645d99) changes only proof elaboration.
The proved private `tensor_hom_global_component` performs the global-cochain
calculation over an abstract site and ring sheaf with an arbitrary degreewise map
satisfying its pure-tensor condition. The public theorem specializes that calculation,
avoiding repeated scheme-instance rewriting. Surjectivity supplies an abstract
section, redundant aliases are removed, and the final equation is applied directly.
The proved private `normalized_projection_eq` identifies the two projection APIs;
its reflexivity proof retains the right-hand constant. Both projection definitions
remain locally irreducible in subsequent calculations. The normalized-factor
reflexivity proof also keeps its definition folded.

Artifact-producing evidence under the unchanged 60-second limit: `lcompile.py --all`
on `scratchpad/repair-generic-right` compiled the repaired module in 51.0 seconds and
the unchanged direct importer `Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom`
in 10.9 seconds. The fresh independent set `scratchpad/verify-final` compiled the repaired module
in 45.7 seconds and the importer in 9.6 seconds, without warnings. The identical
repaired source in both sets has SHA256
`e08c670503a1e105ea6b6b69ee328868568487052fa81d07c7bd9e832d7de22f`. Both sets produce all module companions in their own
`.lbuild`, which the importer uses. The earlier 48.9/54.1-second claims did not
establish this; an intermediate version also timed out on repetition and was replaced.
No consumer adaptation, definition change, profiling option, admission, or skipped
check is part of the repair.

## Old

```lean
theorem normalizedTensorHomCochains_component (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (c : Cochain P (homComplex (R := X.sheaf) L I) 0)
    (p r n : ℤ) (h : p + r = n) (h' : r + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p r n h ≫
        (normalizedTensorHomCochains X P L I 0 c).v n n (add_zero n) =
      (β_ (P.X p) (L.X r)).hom ≫
        (SheafOfModules.tensorHomEquiv (L.X r) (P.X p) (I.X n)).symm
          (c.v p p (add_zero p) ≫ homTensorProjection X.sheaf L I p r n h')
```

The old body was `by sorry`, and there was no private tensor-helper section.

## New

```lean
theorem normalizedTensorHomCochains_component (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (c : Cochain P (homComplex (R := X.sheaf) L I) 0)
    (p r n : ℤ) (h : p + r = n) (h' : r + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p r n h ≫
        (normalizedTensorHomCochains X P L I 0 c).v n n (add_zero n) =
      (β_ (P.X p) (L.X r)).hom ≫
        (SheafOfModules.tensorHomEquiv (L.X r) (P.X p) (I.X n)).symm
          (c.v p p (add_zero p) ≫ homTensorProjection X.sheaf L I p r n h')
```

The body is now proved. The added scoped proof context is:

```lean
attribute [local irreducible] SheafOfModules.tensorHomEquiv homTensorCurrySectionMap
  SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  homComplex homTensorDegreewiseMap normalizedHomGlobalCochains
  normalizedHomFactorEquiv normalizedHomProjection homTensorCurryProjection

section TensorHelpers

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} 𝓡
```

The section ends before the public theorem. Its helpers are
`tensor_braiding_comparison`, `tensor_section_braiding`, `tensor_section_uncurry`,
`tensor_section_braiding_uncurry`, `tensor_section_ext`, `normalized_factor_app`, `presheaf_uncurry_braiding_app`,
`normalized_projection_eq`, `curry_condition_reindex`, and `tensor_hom_global_component`.
They occur only in proof terms. Per-declaration options and the proof's typed local
aliases control elaboration and do not alter the public type.

## Users

`tools/downstream.py --uses normalizedTensorHomCochains_component` found only the item
and `Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom` mentioning the declaration.
The full transitive downstream list is recorded below as well. Holders are those in the
checkout's claim records at the time of this repair. No consumer needs an adaptation:
the public signature, visibility, definitions and public imports are unchanged.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | G1 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AdjointTensorAnnihilatorTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineExtensionModelUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnderivedModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | R3 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePerfectMapLift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePerfectPlusShift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffinePullbackSectionsUnitUncancelled` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSectionsCompositionComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | Q2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.CanonicalEvaluationOpenRestriction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartesianTensorDataComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker` | T3 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DQCoheratorAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData` | T4 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenRestriction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageSquareMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackMateSections` | E3 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionUnitIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit` | B2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization` | G2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit` | V3 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedRestrictionEvaluationMateIsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedRestrictionEvaluationMatePostcompBijective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionProjection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DivisorClassCurve` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DivisorPicRepresentative` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | R3 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FlatPrecomposePus` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeneralTheoremOfCube` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenericComponentsSplit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibres` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GenusInvariant` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | R3 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HenselianClopenRestriction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardMorphism` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardSurjective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HorizontalDualityMateCommutativity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HorizontalDualityMatePasting` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HorizontalOrdinaryInverseFixedPasting` | D2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtPullback` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheaf` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheafNonnegative` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalAlignment` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtExterior` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsChartModelFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsComplexUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsExtensionUnitNormalization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsKFlatComparisonIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedExtensionSectionsUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedGlobalExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomAdjunctionIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedGlobalSectionsBaseChangeMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedHomDirectImageComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedInternalHomBaseChangeExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedPullbackSectionsCounitUnit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedSectionsBaseChangeUnitSquare` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedSectionsCompositionCoherence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedSectionsCompositionKInjective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedSectionsLeftUnitNormalization` | T2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedSectionsRightUnitNormalization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedSectionsSquareComparisonCoherence` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenRestrictionClosedMonoidal` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorExists` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectHomGap` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectObjectCompact` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectOpenSupportDetection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectRHomTensorComparisonDual` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectSupportedMapLift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PerfectTensorHomDuality` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardCupProductBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison` | P4 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1IntersectionSection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardH1MultipleLocus` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosed` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardProductOpen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardProductOpenData` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardPullbackEvaluation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperPerfectCompactTests` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperPerfectTransportCompact` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricDirect` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleQCohComparisonLifts` | G2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility` | G4 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVConePresentation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVExactOpenComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVOpenCoefficientTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVPinnedVertexComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMVSESPresentation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSuccessiveBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportOfBounded` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SchemeIsoLiftedComparisonCounit` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SchemeIsoRightAdjointNormalized` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | A2 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericClopen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SelfExtTorDualChart` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SelfExtTorResolutionCore` | J4 | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenUnion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SteinFactorizationAffine` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedOverlapPerfectExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedPerfectFactorization` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedPerfectGenerator` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TensorRoofTransposition` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationProperCoherentSections` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.ConstructibleSheaf.SylowCoverStalkData` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.Paper.GaloisLisseRepresentations` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.Paper.IntegralCoverTrivialCohomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | Same public signature and definitions; no adaptation. |
| `Sheaf.Paper.ZariskiH0ProperHenselianPair` | unclaimed | Same public signature and definitions; no adaptation. |
| `TargetsCheck` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Estimate` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Picard` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.Slicing` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Picard.Scheme` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.TheoremOfCube` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.BaseChange.EtaleDerived` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | ORCHESTRA | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | Same public signature and definitions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | Same public signature and definitions; no adaptation. |

## Status

landed 20261013T224509-L-1470705 2026-10-13 (merge of deliver/G1/Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents)

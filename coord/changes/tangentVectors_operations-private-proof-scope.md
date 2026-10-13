# AlgebraicGeometry.tangentVectors_operations

## Reason

The proof introduces a private namespace of coordinate maps, uniquely determined gluing,
explicit operations, and proved algebraic identities. The static interface checker flags
its new namespace/variable/noncomputable-section commands conservatively. This record
accounts for that flag. Every new definition and lemma is private, and the original
public theorem signature, visibility and imports are unchanged. No downstream signature
or definition changes; no forced adaptation is necessary. No target statement changes.

## Old

Original declaration signature, verbatim:

```lean
theorem tangentVectors_operations
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    let K := X.residueField x
    let D := Spec (.of (DualNumber K))
    let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
    let b := X.fromSpecResidueField x
    let c : Spec K ⟶ D :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    let q : D ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let s : D ⟶ E := Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom)
    let m : K → (D ⟶ D) := fun t => Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (t • (LinearMap.id : K →ₗ[K] K))).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    ∃ a : AddCommGroup T, letI := a;
      ∃ v : Module K T, letI := v;
        (0 : T).val = q ≫ b ∧
        (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
          j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → (θ₁ + θ₂).val = s ≫ Θ) ∧
        (∀ (t : K) (θ : T), (t • θ).val = m t ≫ θ.val)
```

Original surrounding commands: `universe u`, `open CategoryTheory`,
`namespace AlgebraicGeometry`, `end AlgebraicGeometry`.

## New

The same public declaration signature, verbatim:

```lean
theorem tangentVectors_operations
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    let K := X.residueField x
    let D := Spec (.of (DualNumber K))
    let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
    let b := X.fromSpecResidueField x
    let c : Spec K ⟶ D :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    let q : D ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let s : D ⟶ E := Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom)
    let m : K → (D ⟶ D) := fun t => Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (t • (LinearMap.id : K →ₗ[K] K))).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    ∃ a : AddCommGroup T, letI := a;
      ∃ v : Module K T, letI := v;
        (0 : T).val = q ≫ b ∧
        (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
          j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → (θ₁ + θ₂).val = s ≫ Θ) ∧
        (∀ (t : K) (θ : T), (t • θ).val = m t ≫ θ.val)
```

Added scoped commands: `noncomputable section`,
`namespace AlgebraicGeometry.TangentVectorGluing`,
`variable {K : Type u} [Field K]`,
`variable {X Y : Scheme.{u}} (b : Spec (.of K) ⟶ X) (p : X ⟶ Y)`,
and the matching helper-namespace end. These bind only the private helper declarations.
The fully proved theorem is assembled from those explicit operations. No public data
construction refers to a private helper; only the public theorem's proof does.

## Users

`tools/downstream.py` reports the following transitive downstream modules. The sole
other module mentioning the public theorem is
`Sheaf.AlgebraicGeometry.TangentVectorsVectorSpace`; it applies the same unchanged type.
All listed users retain exactly their statements and definitions because the original
public interface is unchanged. No user is edited in this delivery. Claim holders are
from the local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | M2 | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.CotangentSurjectiveOfTangentInjective | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatUnramifiedTangentCriterion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupAdditionTangentDifferential | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentAddition | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentOperations | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentTransport | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GroupScheme.LieLocalDimension | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedCommutatorTangent | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.MultNTangentDifferential | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProductTangentSpaceDirectSum | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RationalCotangentFunctionalRealization | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RationalPointTangentDerivationIdentification | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RationalTangentCoefficientDescent | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RationalTangentCoefficientLinearMap | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RationalTangentCoefficientOperations | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SchemeTangentSpace | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TangentMapLinear | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TangentVectorsVectorSpace | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unchanged public signature and imports; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged public signature and imports; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Unchanged public signature and imports; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Image | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.RankOne | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged public signature and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged public signature and imports; no adaptation. |

## Status

landed 20261013T001614-L-2330210 2026-10-13 (merge of deliver/H3/Sheaf.AlgebraicGeometry.TangentVectorsVectorSpaceOperations)

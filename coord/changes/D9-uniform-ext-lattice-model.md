# AlgebraicGeometry.ProEtale.uniformConstructibleExt_latticeModel

## Reason

Complete the target-filtration argument for the conditional unrefined cutoff of the
repaired rational stratum theorem. The original theorem and both previously proved
partial-clause theorems keep their signatures and proofs unchanged. The original
unconditional cutoff remains disputed, rather than being weakened or silently assumed.

## Old

The new declaration did not exist. The rational estimate was a private proof import:

```lean
import Sheaf.Paper.UniformConstructibleExtRational
```

## New

The rational estimate is a public import because the new statement uses its actual
`RationalExtIntegralLattice` and `rationalExtIntegralInclusion`. This exports the existing
lattice construction; no replacement predicate or arbitrary lattice data is introduced.

```lean
public import Sheaf.Paper.UniformConstructibleExtRational
theorem uniformConstructibleExt_latticeModel
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) S))
    (hL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) L) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (f : Profinite.continuousMapRingSheaf.{u} E ⟶ Λ),
      ((∃ h : Profinite.continuousMapRingSheaf.{u} E = Λ, f = eqToHom h) ∨
        ∃ h : Profinite.padicAlgClCondensedRing.{u} ℓ = Λ,
          f = Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E ≫ eqToHom h) ∧
      ∃ Lmodel : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) S),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E) Lmodel ∧
      Nonempty ((Mod.extendScalars ((upperStarFromPoint S).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))).obj Lmodel ≅ L) ∧
      (Nonempty (RationalExtIntegralLattice
        ((upperStarFromPoint S).map (rationalExtIntegralInclusion ℓ E)) Lmodel) →
        ∃ d : ℕ,
          (d : WithTop ℕ) = relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
            cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2 ∧
          ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
            ∀ q : ℕ, d < q →
              Subsingleton (Abelian.Ext
                ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i).obj
                  ((CondensedRing.openImmersionLowerShriek
                    (coefficientHeartRingObj Λ) v).obj L)) N.obj q))
```

The theorem chooses the finite coefficient model before any target and proves the
conditional displayed bound by covariant Ext exactness along the actual target filtration.
It creates no data definitions and no new holes.

## Users

The source-only `tools/downstream.py Sheaf.Paper.UniformConstructibleExt --uses
uniformConstructibleExt` scan reported 486 transitive importers before this change.
The following current source import graph lists every transitive importer. No existing
signature, definition, instance, or attribute changes. No consumer is adapted. The two
direct importers were accepted by the server compile service against the changed module
(all three files in the compile set returned exit code 0). Their unchanged temporary
copies have been removed. The holder column does not
claim that these modules are unclaimed: this remote mirror has no holder recorded for
them, and none is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Challenge | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| TargetsCheck | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.UniformConstructibleExt | D9 | Adds a proved conditional clause and exports the lattice types it uses. |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.GeometricConstituentOrbit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AdmissibleVerdierExchange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AffineCounitScalar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AffineLineAdjunctionAssembly | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.AffineSpaceRationalInduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.BrownExceptionalAdjoint | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.BrownHypothesesGeneration | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ChartCounitScalarTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CoefficientUnitTowerNormalized | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CompactSupportTowerReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CompositionComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedExceptionalReconstruction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedHomChainRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedOpenCoefficientModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedOpenCounitComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedOpenCounitRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedOpenCounitUnits | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.CondensedOpenUnitComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ConstructibleCompactness | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleCtfChartDomain | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.EtaleSumCounitScalar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalRealizationNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalReconstructionComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalReconstructionContext | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalFiniteCompatibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalNormalizedAdjoints | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemComponents | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemDomains | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemIso | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExceptionalSystemLaws | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionIntegralDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionIntegralModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionLimitEquations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionRationalComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionRationalDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionRationalModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionReductionDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionReductionLimits | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionSourceNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionStrictLimits | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldExtensionTowers | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemHeart | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldOrientationSystemRigidity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldProjectionOpenSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldProjectionProperSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldProjectionSystemData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldProjectionSystemSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldProjectionTensorConstruction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldPuritySystemTranspose | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldPurityTransposeArrows | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSupportEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemCocycle | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemCoherence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemMixed | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FieldShriekSystemTransitions | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteCompactSupportDomains | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteOrientationReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteProjectionOperationPresentation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteSupportCompositorCoefficient | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteSupportCompositorExistence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteWindow | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteWindowBounded | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.FiniteWindowUnbounded | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralAdjunctionBijection | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralCoefficientModelComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralCompositorLimitRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralDirectImageTower | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralReconstructionComparisonData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralReconstructionComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralStageProjectionReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.IntegralTowerImageReconstruction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.MateOpenCompactSupportExchange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.MateOpenProperRestrictionIso | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.MateOpenRestriction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.MateOpenRestrictionMaps | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.NonrationalCompositionSeed | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OpenExceptionalScalarLocality | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OpenProEtaleCounitScalar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OrderedLineLevelBounds | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OrderedTateScalarNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OrderedTowerOrientation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OrientationGroundFieldRetagging | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.OrientationScalarTowerTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.P1CounitScalar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.P1SplittingScalar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ProjectionFiniteReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ProperExceptionalRestriction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.PulledOrderedLineSingle | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.PurityConjugatesTowerReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.PurityFiniteReductionTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.PurityPullbackLevelBounds | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.PurityPullbackReductionTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.PurityTowerReductionComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RationalAffineTensorCalculus | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RationalExceptionalRestriction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RationalP1Triangle | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RationalRestrictionGlue | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RawChartScalarCounitPasting | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RestrictionLocal | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCompositionFactors | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerBound | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerChartData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerGamma | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerGammaData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerGluing | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerGluingData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerP1Data | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TensorTransposeTowerNaturality | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerAdjointCompositorRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerGeometricPurityMate | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerNormalizationPreservation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerOrientationEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1CtfData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1DiagonalTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1FirstTraceReordering | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1FixedTotalTensor | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1GeometricCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1KernelScalarData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1LevelCtfModel | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1LevelWords | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1ProperCtf | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1PushCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1SecondTraceReordering | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1SingleLevelData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1SingleLevelTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1TensorCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1TriangleFactorization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1TriangleWords | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1UniformCtfDomains | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerP1UniformPresentation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerPurityAdjointTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerTensorAdjointDomains | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerTensorTransposeWords | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TowerUniformEtaleDomains | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackCofinalModels | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackLineMembership | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackReductionData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackReductionTower | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackTateReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackTowerBounds | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackTowerDomain | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.UniformTowerTensorClosure | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.VaryingRingGraphSummand | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.VerdierCoefficientRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Paper.VerdierExchange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.Reduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionExceptionalConservativity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionExceptionalRealization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionOrientation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralKernelContractions | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctors.ScalarSixDirectImage | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.SmoothPurity.NormalizedWitness | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Targets.AffineSpaceRationalLine | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Targets.PoincareUncurry | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| Sheaf.Targets.SmoothPurityQbar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.PoincareDuality.Poincare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.PoincareDuality.Verdier | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.SmoothPurity.Defs | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.Statement | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Additivity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Basic | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.BorelMoore | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.CompactCohomology | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.CompactPullback | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Correspondence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.CorrespondencePair | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.CurvePieces | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Dualizing | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FibreCoherence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FibreModel | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FixedPoint | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FixedPointScheme | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Frobenius | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.GenericQuotient | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.HomologyUnit | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.KunnethVerdier | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.LocalTerm | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.LocalTermLocality | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Main | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ModelExtension | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.OpenSquare | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.PointNormalization | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Product | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ProperCompatibility | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ProperCurve | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ProperPushforward | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.PullbackFamily | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.RelativeFrobenius | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Stalk | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.Statement | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.SupportedPairing | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.TraceClass | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.WeilBaseChange | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.TraceFormula.WeilTrace | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.WeilSheaf.Curve | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.WeilSheaf.EulerProduct | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.WeilSheaf.LFunction | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.Examples | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.LissePurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.Rationality | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.Weights | not recorded in this mirror; not adapted | Existing interface retained; no edit. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not recorded in this mirror; not adapted | Existing interface retained; no edit. |

The new theorem has no existing callers. Textual uses of `uniformConstructibleExt` remain
local to the item, and the original theorem's elaborated type is unchanged. No target
statement or definition used by a target changes.

## Status

landed 20261026T130343-L-3450712 2026-10-26 (merge of deliver/D9/Sheaf.Paper.UniformConstructibleExt)

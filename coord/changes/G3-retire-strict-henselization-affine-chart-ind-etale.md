# AlgebraicGeometry.Scheme.strictHenselization_indEtale_of_affine_chart

## Reason

Retirement item in coord/retire-items.tsv, approved by the human on 2026-10-20.
The upstream twin proves the same mathematical result using the full affine-neighbourhood
colimit, whereas the old copy and its consumers use a small representative colimit.
A literal import swap fails: the full structural-map extension and the small-model
Sheaf API both export strictHenselizationStructuralMap_eq with different types.
It also meets stale compiled imports of the already retired Sheaf.StrictHenselization.

Withdraw the old copy. SmallStrictHenselizationIndEtale privately imports the upstream
twin, proves structural-map compatibility for smallStrictHenselizationColimitIso,
and applies the upstream theorem to the transported spectrum isomorphism. Its distinct
public corollary name permits both APIs to coexist without exporting the conflicting
full-model helper. This is a proved transport, not a renamed copy of the original
triples-colimit argument. No source-library file or target statement changes.

## Old

```lean
theorem strictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictHenselizationStructuralMap s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A
```

## New

The original node points to the existing upstream theorem, whose signature is:

```lean
theorem strictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictLocalization s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictLocalizationToBase s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A
```

The small-model consumers use the proved transport corollary:

```lean
theorem smallStrictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictHenselizationStructuralMap s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A
```

Its hypotheses, universe, algebra structure and conclusion equal the old copy's;
only its name differs. The upstream theorem stays verbatim. All 17 live direct
consumers migrate their import; 12 theorem calls use the new name. Existing consumer
signatures and definitions stay verbatim. DAG proof dependencies of adapted consumers
point to the corollary node, which in turn cites the upstream theorem's original node.
Other mathematical citations of the original node remain valid via the same canonical
model comparison. The unit's statement and realized proof steps are retained.

The import change also enables the private-module linter in
Sites.AffineLineInfinityStrictLocalModel, whose public statement is already taken out.
Disable that one linter in this intentionally private helper module; no declaration changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.EtaleSectionGermSpecialization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed (quarantined) | No restoration or edit. Preserve its archived source, Lean attachment and dependencies; the proved small-model corollary supplies the equivalent chart API when restored. Not withdrawn. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnitGerm | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityStrictFibreComparison | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LogBlowupNormalization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.LogSmoothLogRegular | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Import the new proved small-model corollary module; rename the identity-chart theorem call in the existing private flatness proof. All signatures and the finite-etale assembly stay unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Migrate the private import and identity-chart call in the existing private flatness proof to the proved small-model corollary; all signatures and other proof lines stay unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleStalkConservative | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleVanishingDetection | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.ProjectiveStrictLocalIntersectionAcyclic | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SfFullCdWeaklyContractibleTest | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.AffineInfinityBoundarySupport | unclaimed (quarantined) | No restoration or edit. Preserve its archived source, Lean attachment and dependencies; the proved small-model corollary supplies the equivalent chart API when restored. Not withdrawn. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialHigherProjectionSupport | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialInductionStep | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.AffinePolynomialProjectionSupport | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeff | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffFractionTrdeg | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictHenselizationLimit | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseGeometry | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseGlobalGerms | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseIndEtale | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseSections | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalCoefficientPresentation | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreDerivedUnit | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalFibreUnitStalks | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.AlgebraicGeometry.StrictLocalGeometricFibreTest | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.FiniteAffineDirectImageSupportBound | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.GeometricStalkPerfect | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.FiniteBaseStrictLocalization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.LogRegularDesingularization | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.LogRegularToricRefinement | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.SmoothGeometricStalkAlgebra | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.TraceFormula.SmoothSourceConstructibleLocalAcyclicity | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |
| Sheaf.TraceFormula.StrictHenselizationQuasiFiniteRing | unclaimed | Import the new proved small-model corollary module; rename any affine-chart theorem calls. |
| Sheaf.TraceFormula.StrictHenselizationTensorFinite | unclaimed | Indirect consumer: no edit; existing signatures and small-model constructions are preserved. |

## Status

landed 20261021T061122-L-1709106 2026-10-21 (merge of deliver/G3/Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale)

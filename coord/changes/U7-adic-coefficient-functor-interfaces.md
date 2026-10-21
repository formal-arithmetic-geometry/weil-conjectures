# AlgebraicGeometry.Scheme.reductionChange and derived specification interfaces

## Reason

Repeated expansion and comparison of the nested scalar-extension existential witnesses
made the complete file exceed the compile limit. Name the exact ordinary and derived
specifications. The object, map, additivity and counit APIs use those named
specifications. Both public functor bodies retain their original witness aliases.
Functor aliases become definitions so proof-local irreducibility protects calculations.
The original derived-category instance bodies are preserved.

No mathematical statement or target changes. These definitions used by targets are
submitted for independent statement review. The named predicates unfold to the old
predicates. Both chosen functors retain their original bodies. The counit is selected from
the same derived-pair specification; naming its predicate changes no witness,
by proof irrelevance. No arbitrary new data is selected.
The completed coefficient dependency is unchanged by this delivery.

The 45a4a4cec1 return concerns the reviewer-fix filename, not a missing repository
record. This record is delivered at
`coord/changes/U7-adic-coefficient-functor-interfaces.md`. If a reviewer supplies
an override through `--apply-fixes`, the loader expects the flat filename
`U7-adic-coefficient-functor-interfaces.change.md` (see `tools/batch_land.py`,
`fixes`). The repository filename must retain its ordinary `.md` suffix.
The consumer table has been regenerated from the current source and claims,
including the textual user `PbcUniformCompleteTriangulated` checked by preflight.

The current return is for head `7754223355`: review passed, but landing tried
to read the absent `Sheaf.Algebra.Homology.DerivedCanonicalFiltration` source.
Its `coord/rework.tsv` row preserves that module in quarantine. This delivery
does not change or withdraw it, its node, or any of its dependencies. The
retained item has been compiled against the current published server build;
`deliver3.py` creates the replacement commit on freshly fetched `sheaf-dag`.

## Old

```lean
noncomputable abbrev reductionChangeExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  completedAdicChangeData T φ
```

```lean
noncomputable abbrev reductionChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionModules T R ⥤ reductionModules T S := completedAdicChange T φ
```

```lean
noncomputable instance reductionChangeAdditive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionChange T φ).Additive :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose
```

```lean
noncomputable def reductionDerivedExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ (LF : reductionDerivedCategory T R ⥤ reductionDerivedCategory T S)
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (reductionModules T R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (reductionModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

```lean
noncomputable abbrev reductionDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionDerivedCategory T R ⥤ reductionDerivedCategory T S :=
  completedAdicDerivedChange T φ
```

```lean
noncomputable def reductionDerivedCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    DerivedCategory.Qh ⋙ reductionDerivedChange T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (reductionDerivedExistence T φ).choose_spec.choose
```

```lean
noncomputable instance reductionDerivedUniversal (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionDerivedChange T φ).IsLeftDerivedFunctor (reductionDerivedCounit T φ)
      (HomotopyCategory.quasiIso (reductionModules T R) (ComplexShape.up ℤ)) :=
  (reductionDerivedExistence T φ).choose_spec.choose_spec.1
```

## New

```lean
def reductionChangeSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionModules T R ⥤ reductionModules T S) → Prop :=
  (fun {B : Type (t + 2)} {P : B → Prop} (_ : ∃ x, P x) ↦ P)
    (completedAdicChangeData T φ)
```

```lean
def reductionDerivedSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (LF : reductionDerivedCategory T R ⥤ reductionDerivedCategory T S) : Prop :=
    ∃ (ε : DerivedCategory.Qh ⋙ LF ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (reductionModules T R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (reductionModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
```

```lean
theorem reductionChangeExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ E, reductionChangeSpec T φ E := completedAdicChangeData T φ
```

```lean
noncomputable def reductionChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionModules T R ⥤ reductionModules T S := completedAdicChange T φ
```

```lean
noncomputable instance reductionChangeAdditive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionChange T φ).Additive :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose
```

```lean
theorem reductionDerivedExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ LF, reductionDerivedSpec T φ LF :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

```lean
noncomputable def reductionDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionDerivedCategory T R ⥤ reductionDerivedCategory T S :=
  completedAdicDerivedChange T φ
```

```lean
noncomputable def reductionDerivedCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    DerivedCategory.Qh ⋙ reductionDerivedChange T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (reductionDerivedExistence T φ).choose_spec.choose
```

```lean
noncomputable instance reductionDerivedUniversal (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionDerivedChange T φ).IsLeftDerivedFunctor (reductionDerivedCounit T φ)
      (HomotopyCategory.quasiIso (reductionModules T R) (ComplexShape.up ℤ)) :=
  (reductionDerivedExistence T φ).choose_spec.choose_spec.1
```

## Users

The table records all modules listed by the transitive downstream query, plus the
item. Direct textual users of any changed interface are identified. The meaning
of every statement stays the same because the changed definitions are definitionally
equal to their originals. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | same definitions; transitive user |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | same definitions; transitive user |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | same definitions; transitive user |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | same definitions; transitive user |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | N3 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C3 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProEtaleConstantScalarPullbackCube | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClosedExtension | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | P4 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | G4 | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ProperOpenSiteTransport | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SfFullcdUsedClass | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | same definitions; transitive user |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | Q2 | same definitions; transitive user |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | same definitions; transitive user |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | J3 | same definitions; transitive user |
| Sheaf.Paper.AdicCoefficientDatum | U7 | same definitions; direct textual user |
| Sheaf.Paper.AdicCoefficientDatumCompleted | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AdicCohomologyTorsionNormalForm | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AdicGlobalDerivedHom | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AdicReductionCohomologySequence | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | K4 | same definitions; transitive user |
| Sheaf.Paper.AdicTorFlatCriterion | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AdmissibleLattices | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | same definitions; transitive user |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | same definitions; transitive user |
| Sheaf.Paper.BoundedConstructibleComplete | unclaimed | same definitions; transitive user |
| Sheaf.Paper.BoundedConstructibleTower | unclaimed | same definitions; transitive user |
| Sheaf.Paper.BoundedSiteAdjunctionTranspose | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CoefficientSystemDerivedComparison | B4 | same definitions; transitive user |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompactSupportExchangeTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompactSupportSiteCoherence | H4 | same definitions; transitive user |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedConstantAlgebraFlatQuotients | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedConstantCoefficientEquivalence | unclaimed | same definitions; direct textual user |
| Sheaf.Paper.CompletedConstantConstructibility | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedConstantFiniteComplexRealization | E4 | same definitions; transitive user |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedConstantSheafReduction | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedDerivedInverseLimit | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedDirectImageLimits | P5 | same definitions; transitive user |
| Sheaf.Paper.CompletedExtensionZeroComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedFiniteReductionTensorComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedFiniteReductionTensorModel | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedKoszulQuotientComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedKoszulReductionRoosTriangle | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedProjectionCoherence | D2 | same definitions; transitive user |
| Sheaf.Paper.CompletedPullback | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | same definitions; transitive user |
| Sheaf.Paper.CompletedQuotientUnitNormalization | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedReconstructionUnitComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedRlimFunctor | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedScalarShift | F3 | same definitions; transitive user |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedTowerDerivedLimitFunctor | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedTowerDirectImage | unclaimed | same definitions; transitive user |
| Sheaf.Paper.CompletedTowerPullback | unclaimed | same definitions; direct textual user |
| Sheaf.Paper.CondensedAmbientExchange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | K1 | same definitions; direct textual user |
| Sheaf.Paper.ConstructibleCoefficientHomologyTriangulated | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ConstructibleCoefficientSerre | unclaimed | same definitions; transitive user |
| Sheaf.Paper.DirectImageCtfOpenTor | unclaimed | same definitions; transitive user |
| Sheaf.Paper.EtaleIntegralLineReductions | unclaimed | same definitions; transitive user |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ExactFunctorDerivedLimit | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | U1 | same definitions; transitive user |
| Sheaf.Paper.ExceptionalMateSiteComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteCoefficientDerivedOriginPresentation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteCoefficientIntrinsicConstructibility | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteFieldLocalTensorModel | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteFieldSheafScalarExtension | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | same definitions; transitive user |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteLevelAmplification | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteLevelProEtaleBaseChange | J4 | same definitions; transitive user |
| Sheaf.Paper.FiniteLevelRectangle | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteMittagLeffler | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FinitePerfectAdicRealization | W3 | same definitions; transitive user |
| Sheaf.Paper.FiniteProjectiveTensorProducts | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteReductionPullbackCoherence | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteRingCompactSupportProjection | H1 | same definitions; transitive user |
| Sheaf.Paper.FiniteRingCompactSupportProjectionMap | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FiniteStagePairCategory | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FourArrows | unclaimed | same definitions; transitive user |
| Sheaf.Paper.FourCorners | unclaimed | same definitions; direct textual user |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | same definitions; transitive user |
| Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralHomAugmentedTowerComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralHomComparisonIsIso | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralHomReduction | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralHomReductionTowerComponents | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralHomRoosTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntegralUniformCoefficient | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntrinsicCompletion | unclaimed | same definitions; transitive user |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | same definitions; transitive user |
| Sheaf.Paper.LevelwiseAdicTruncations | K2 | same definitions; transitive user |
| Sheaf.Paper.LisseCompletedPointwiseComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.LisseCompletedSystemComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.LisseCompletedSystemData | unclaimed | same definitions; transitive user |
| Sheaf.Paper.LisseCompletedTensorOperations | unclaimed | same definitions; transitive user |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NearbyClosedImage | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NearbySpreadOut | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalCompletedIntegralModel | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedEtaleOriginWitnesses | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedOriginComparisonCoherence | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedOriginScalarComparisons | unclaimed | same definitions; transitive user |
| Sheaf.Paper.NormalizedTowerCommonLisseStrata | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcActualRingedExchange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcActualScalarPullback | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcAutomorphismTransport | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcCompletedPullbackActual | unclaimed | same definitions; direct textual user |
| Sheaf.Paper.PbcExactCompletionData | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcFiniteCompletedCoefficientMap | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcFinitePullbackConstructibility | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcRationalCategory | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcUniformLocalModelCohomology | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcUniformReductionCriterion | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcUniformReductionProfile | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcWeilCategory | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PerfectProjectionFormula | T7 | same definitions; transitive user |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointDerivedHomEvaluation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointDerivedHomModels | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointExtensionKFlat | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointHomComplexAdjunction | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointReductionUnits | A9 | same definitions; transitive user |
| Sheaf.Paper.PointSectionsDerivedReduction | A6 | same definitions; transitive user |
| Sheaf.Paper.PointSectionsFiniteReduction | R1 | same definitions; transitive user |
| Sheaf.Paper.PointSectionsFiniteness | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointSectionsFinitenessIntegral | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointSectionsIntegralCohomologyControl | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointSectionsScalarExtension | G3 | same definitions; transitive user |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointSheafHomMaps | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PointTensorHomEvaluation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ProEtaleConstantReductionTower | B3 | same definitions; direct textual user |
| Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ProperBaseChangeFourArrows | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ProperOpenCoefficientMate | U3 | same definitions; transitive user |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ProperOpenTowerComparison | P1 | same definitions; transitive user |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PurEtaleScalarMateProjection | M7 | same definitions; transitive user |
| Sheaf.Paper.PurityFrameClass | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PurityFrameKummer | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | same definitions; transitive user |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | same definitions; direct textual user |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed | same definitions; transitive user |
| Sheaf.Paper.RingedEtaleOriginWitness | unclaimed | same definitions; transitive user |
| Sheaf.Paper.ScalarPullbackComposition | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SequentialDerivedInverseLimit | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SequentialDerivedInverseLimitCompleted | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SfCompactSupportRestrictionOfScalars | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | same definitions; transitive user |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | N2 | same definitions; transitive user |
| Sheaf.Paper.StrictTowerOperations | unclaimed | same definitions; transitive user |
| Sheaf.Paper.SystemTensorMateArrows | R3 | same definitions; transitive user |
| Sheaf.Paper.TateInverseLimitBaseChange | unclaimed | same definitions; transitive user |
| Sheaf.Paper.TowerPreservation | unclaimed | same definitions; transitive user |
| Sheaf.Paper.UniformCompleteTriangulated | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilCompletedCechComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilCompletedKoszulLimitComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilCompletedKoszulProductComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilCompletedKoszulRepresentativeComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilCompletedKoszulRoosComparison | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilCompletedTensorReflector | unclaimed | same definitions; transitive user |
| Sheaf.Paper.WeilTensorProduct | X2 | same definitions; transitive user |
| Sheaf.SecSmoothPurity.ConstantScalarPullbackSquare | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.DirectImageScalarOperations | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.OpenScalarExchange | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore | unclaimed | same definitions; transitive user |
| Sheaf.SecSmoothPurity.TensorPullbackSquare | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.ClosedCostalkDuality | V4 | same definitions; transitive user |
| Sheaf.SixFunctors.EtaleOpenKFlat | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | same definitions; transitive user |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | same definitions; transitive user |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | same definitions; transitive user |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | same definitions; transitive user |
| Sheaf.Paper.PbcUniformCompleteTriangulated | unclaimed | same derived specification; direct textual user |

## Status

landed 20261021T005753-L-1891154 2026-10-21 (merge of deliver/U7/Sheaf.Paper.AdicCoefficientDatum)

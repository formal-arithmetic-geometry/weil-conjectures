# AlgebraicGeometry.Etale.coefficientUnitDerived

## Reason

The reflexivity proof identifying coefficientUnitDerived with the canonical degree-zero
unit map exceeded the kernel heartbeat diagnostic, and the item exceeded the 60-second
file limit. Its body expanded the exact-functor degree-zero comparison. Reuse the named,
generic exactDerivedScalarUnitMap instead, so this equality checks without expanding that
comparison. This is the identical composite, with the identical source and target.
GeoCartierCoeffExtension was unclaimed when edited. The new public import supplies the
real construction used in its definition; import_direction.py confirms no cycle.

## Old

```lean
noncomputable def coefficientUnitDerived {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedConstantDerived (A := A) i ⟶
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj
        (supportedConstantDerived (A := B) i) :=
  (DerivedCategory.singleFunctor
    (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map
      (coefficientUnitModule φ i) ≫
    ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
      (supportedConstantModule (A := B) i)
```

## New

```lean
noncomputable def coefficientUnitDerived {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedConstantDerived (A := A) i ⟶
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj
        (supportedConstantDerived (A := B) i) :=
  exactDerivedScalarUnitMap (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (coefficientUnitModule φ i)
```

## Users

The downstream scan found 239 transitive importers and only the defining module using
coefficientUnitDerived directly. The assigned item is an additional new user, included
below. No statement changes meaning: expanding exactDerivedScalarUnitMap gives the old
body exactly. Every existing signature and visibility is retained. No consumer edit is
needed beyond the assigned item. The independent reader should recheck target meaning
for this definition change, together with the scalar-unit packaging repair.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Supplies the new named map; its parallel representation repair is recorded in M4-supported-derived-scalar-unit-structure.md. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | E8 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | D2 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | M4 | New proof uses the defining equation without expanding the composite. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ChernFlagFormula | G4 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.DiagonalTowerLimit | S9 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.DiagonalTowerSystem | W6 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.LocalizedTopChern | E5 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.SfBidualityClass | C6 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassChern | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassFinite | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassProjective | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassPullback | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassReduction | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassSystems | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.WeilFourierInversion | J6 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.WeilOne | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Use the named canonical derived-unit map; signature, normalization and theorem unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SixFunctors.RationalVerdier | V4 | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.Statement | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No term-level use; the imported map and statements retain their meaning; no edit. |

## Status

landed 20261019T231236-L-565115 2026-10-19 (merge of deliver/M4/Sheaf.AlgebraicGeometry.SupportedKummerScalarSource)

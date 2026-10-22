# Sheaf.AlgebraicGeometry.SupportSiteComparison

## Reason

Fill all eight theorem holes while preserving the existing public interface. The static
checker requests a record because the private proofs add scope and elaboration commands.
No target statement, mathematical definition, source-library module or consumer changes.
The two existing node records are updated to the proof route actually used.

Generic derived tensor and quotient-mate helpers perform categorical calculations before
specializing to concrete sheaves. Retaining type transparency avoids repeated unfolding
of concrete sheaf constructions. All helpers are proved and private.

## Old

The original module has eight theorem bodies containing `sorry`. For example, this is the
original first theorem verbatim:

```lean
theorem supportComparisonUnit_existsUnique :
    ∃! c : etaleSupportKernel A i ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportSections i A,
      ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        c.app F ≫ kernel.ι
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
            (supportRestrictionArrow i).op) =
        (Sheaf.supportedSectionsInclusion T.smallEtaleTopology
          (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)).app F ≫
          (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 T)))) := by
  sorry
```

The original module has no `CoefficientNormalization` or `ExteriorComparisonProof`
sections, no private canonical constant-functor monoidal instances, and no generic
proof helpers. All 28 public signatures and 20 definition bodies of that version remain
verbatim in the new version, as do its public imports and original docstrings.

## New

All eight theorem proofs are complete; no new hole or public declaration is introduced.
The first theorem keeps exactly the signature above, replacing only its proof body;
the other seven existing theorem signatures and all existing data bodies also stay verbatim.

The private coefficient proofs introduce the following local instances:

```lean
private noncomputable local instance canonicalConstantEt
private noncomputable local instance canonicalConstantPro
```

These lines identify the helper declarations; their full proved definitions are in the
item module. They wrap the existing canonical constant-sheaf monoidal structures. The
exterior proof section enables them with:

```lean
attribute [local instance] canonicalConstantEt canonicalConstantPro
```

Other `variable`, `open`, local-instance and elaboration-option commands support the
private categorical proofs. Their sections use the existing native monoidal sheaf
structures, locally disabling redundant supported-sheaf tensor instances. They do not
change the public formulas or their mathematical meanings. No new global instance is
exported. The unit-route import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` remains.
The removed private proof imports are listed in `report.md`.

## Users

No existing signature or definition changes, so no consumer adaptation is necessary.
The table records the item and every current transitive downstream module reported by
`tools/downstream.py`. Its `--uses canonicalConstantEt canonicalConstantPro` check finds
zero existing users of either new private helper. Holders are recorded at packet revision.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | D9 | Eight proof holes closed; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.SupportComparisonSectionModel` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.AlgebraicGeometry.SupportedFullSupportProduct` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityDivisorClass` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PurityFrameIndependence` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RegularImmersionCancellation` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RegularImmersionClassData` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RegularImmersionExteriorClass` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RegularImmersionPurity` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RegularImmersionSignedEvaluation` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.RelativeSupportBottomDescent` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | No adaptation: public signatures, data and imports unchanged. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No adaptation: public signatures, data and imports unchanged. |

## Status

landed 20261022T022029-L-430341 2026-10-22 (merge of deliver/D9/Sheaf.AlgebraicGeometry.SupportSiteComparison)

The complete eight-proof candidate compiled in 49.8 seconds, and the actual item path
compiled in 57.0 seconds before restricting the two helper instances to local scopes.
The final local-scope version is checked by delivery preflight. A source comparison
confirms all 28 public signatures, 20 data bodies, and public imports unchanged. No new
nodes, holes, public declarations, withdrawn modules, or forced adaptations are introduced.

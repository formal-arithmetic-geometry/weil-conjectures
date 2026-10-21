# Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram

## Reason

The assigned module is explicitly listed as a retire item in coord/retire-items.tsv.
The reviewed D2 canonicalization already moved both DAG attachments upstream on
2026-10-20. The current Sheaf file is a declaration-free re-export, with zero holes.
Retire this redundant path and migrate its one remaining direct consumer.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram

/-! # The raw cohomology diagram

Source: Stacks Project, Tag 09Z1, the canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).
-/

@[expose] public section
```

The consumer RawModuleScalarPullbackComparison has this public import:
```lean
public import Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram
```

## New

Withdraw the redundant shim using deleted.txt; the delivery tool writes an empty
module. In RawModuleScalarPullbackComparison replace only the import above with:
```lean
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
```

The old shim re-exported exactly this upstream module, so the consumer retains
exactly the same public declarations and instances. Its signatures, definitions,
proofs and all other imports are unchanged. No upstream file is modified.
Both DAG nodes retain their upstream Lean attachments and all mathematical fields;
only lean.note records the retirement. No target meaning changes.

## Users

The exact-import search of lean/Sheaf, lean/WeilConjectures and quarantine finds
one direct importer: RawModuleScalarPullbackComparison (unclaimed). It is adapted
in this packet. tools/downstream.py lists the following transitive users:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceConstruction | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierComplementFrame | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierPoleBoundary | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierProIntegralDerivedUnit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierProIntegralResidueDerivedUnit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierProIntegralScalar | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierProKummerDerivedUnit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierProRootScalar | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionData | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonConstantGenerator | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonForgetScalars | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCup | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassInjectivity | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | P4 | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | G4 | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison | unclaimed | Replace the public shim import by its identical upstream re-export. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedIntegralResidueSequence | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryPullback | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerChernRealization | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarDerived | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarMaps | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.AffineLineSupportGeometry | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Transitive consumer; same upstream public environment, no adaptation. |

The historical retirement inventory also names HigherDirectImageRawComplexPresentation,
RawModuleAbelianHomComparison, RawModuleRestrictedAbelianNaturalIso,
RawModuleRestrictedAbelianNegative and RawModuleRestrictedAbelianNonnegative.
Their current sources no longer import this shim; no changes are needed.
There is no rework row for the item and no quarantined importer is removed.

The DAG parents retain all references to the two nodes: lem-sbc-restricted-over-abelian-complex-data, sbc-lem-higher-image-raw-affine-image-rep, lem-sbc-raw-module-restricted-abelian-nonnegative, lem-sbc-raw-module-scalar-hom-composite-formula, lem-sbc-raw-scalar-pullback-formulas, lem-sbc-raw-module-abelian-hom-comparison, lem-sbc-higher-image-raw-complex-presentation, def-sbc-raw-module-scalar-source-prefix, def-sbc-higher-image-raw-diagram, def-sbc-raw-module-abelian-hom-map, lem-sbc-raw-module-restricted-abelian-natural-iso, def-sbc-raw-module-scalar-pullback-comparison, lem-sbc-raw-module-restricted-abelian-negative, lem-sbc-raw-scalar-pullback-module-formula, sbc-lem-higher-image-raw-affine-class-vanishing.
They still obtain the same declarations from the canonical upstream module.
The unit sk-lem-failure-field has empty realized.statement and realized.steps;
no unit route requires the redundant module path. Its mathematics is preserved.
There is no current V1 return for this item.

## Status

landed 20261021T014725-L-2448335 2026-10-21 (merge of deliver/V1/Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram)

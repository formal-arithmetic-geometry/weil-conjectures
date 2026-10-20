# supportedSheaf_smallColimitsGeneric and supportedSheaf_intColimitsGeneric

## Reason

The delivery closes two original theorem holes without changing any existing signature or
non-theorem body. Exactness follows from the already stated normalized ordinary adjunction;
its declaration and two instances move after that adjunction so the dependency is acyclic.

The preflight conservatively flags new commands and the two public helper declarations.
The helper propositions cache the existing Mathlib sheaf-colimit construction for instance
search inside this module. They are public because public definitions use these proof
arguments. Their instance registration is explicitly local, so importing modules receive no
new global instance. The data constructed by all existing definitions is unchanged up to
proof irrelevance. No target's mathematical meaning changes and no target review reopens.

Synchronous checking avoids deferring proof tasks until the axiom probe. A scoped linter
setting retains the original unused flat-resolution parameter of the complex identity.
Neither setting disables kernel checking, changes elaboration transparency, or raises a limit.

## Old

The existing file setting, verbatim:

```lean
set_option autoImplicit false
```

There were no declarations named supportedSheaf_smallColimitsGeneric or
supportedSheaf_intColimitsGeneric, no local registration of them, no Elab.async setting,
and no scoped unusedSectionVars setting. The existing theorem and instance signatures,
attributes, public imports, and definition bodies are preserved verbatim by the delivery.

## New

Immediately after autoImplicit false:

```lean
-- Check proofs synchronously before the delivery appends its axiom probe.
set_option Elab.async false
```

In namespace AlgebraicGeometry.ProEtale, with the existing universes u v:

```lean
/-- Small colimits of pro-etale sheaves, supplied once to the cochain tensor instances.
Source: Mathlib sheaf colimits
(blueprint: def-pur-proetale-supported-exterior-product). -/
theorem supportedSheaf_smallColimitsGeneric
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (X : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X) C) :=
  ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

attribute [local instance] supportedSheaf_smallColimitsGeneric

/-- Integer-indexed colimits of pro-etale sheaves, using the direct sheaf-colimit instance.
This avoids repeatedly searching through general colimit-shrinking instances when deriving
projection inverse images. Source: Mathlib sheaf colimits
(blueprint: def-pur-proetale-supported-exterior-product). -/
theorem supportedSheaf_intColimitsGeneric
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (X : Scheme.{u}) :
    HasColimitsOfShape ℤ (Sheaf (Scheme.ProEt.topology X) C) :=
  Sheaf.instHasColimitsOfShape

attribute [local instance] supportedSheaf_intColimitsGeneric
```

Only the existing complex identity receives this scoped linter setting:

```lean
-- Retain the existing flat-resolution parameter for compatibility with callers.
set_option linter.unusedSectionVars false in
```

The identity is proved by reflexivity. The exactness proof uses the existing ordinary
adjunction to obtain finite-colimit preservation, and the existing constant-sheaf and
right-adjoint instances to obtain finite-limit preservation. It introduces no statement or
definition change. Five original named theorem holes remain, with no hole added.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
--uses supportedSheaf_smallColimitsGeneric supportedSheaf_intColimitsGeneric` reports
62 downstream modules and zero consumers mentioning either new name. The table includes
all 62 downstream modules and the edited item. Current holders are read from the project
claim records. The local instance attributes and checking/lint options do not propagate
through imports; all existing consumer expressions and statements keep their meaning.
No consumer adaptation is needed or delivered. The maintainer's global build remains the
independent verification of the complete library.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct | W4 | Two proof replacements; local colimit instances and checking settings. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | X2 | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedProductQuotientModel | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Existing API and meaning unchanged; no reference to the new helpers; no adaptation. |

## Status

landed 20261020T211848-L-3511552 2026-10-20 (merge of deliver/W4/Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct)

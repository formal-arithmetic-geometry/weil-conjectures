# AlgebraicGeometry.ProEtale.AffineOrderedIntegration.coefficient_plus

## Reason

The unrestricted auxiliary boundedness assertion is already STATEMENT-DISPUTED in the
published file. Its proof requires an invertible coefficient exponent on Y, but the
statement supplies no structure map or invertibility hypothesis. It is not the DAG
node's assertion: the node works with separated finite-type schemes over P.field.k.
The only caller is integration, which already supplies aY. Remove the unused general
claim and expose the existing fully proved coefficient_plus_on_base theorem for that
caller. This is withdrawal of a disputed auxiliary assertion, not a proof of that assertion.
No target statement or object construction is changed.

## Old

```lean
/-- The finite Tate coefficient is bounded below.
Source: finite Tate lines (blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: the zero coefficient is the constant sheaf in degree zero. Each successor tensors
with a locally free degree-zero Tate line and shifts by two. Induction gives the single
sheaf A(d) shifted by 2d; this also applies on the empty scheme. -/
-- STATEMENT-DISPUTED: the unrestricted base need not have invertible exponent.
-- On a nonreduced base of coefficient characteristic, roots of unity can give
-- nonflat coefficient stalks; repeated derived tensors need not be bounded below.
theorem coefficient_plus (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) :
    DerivedCategory.TStructure.t.plus (etaleCoefficient P Y d) := by
  sorry

```

The existing proved theorem coefficient_plus_on_base was private. The integration definition was:

```lean
def integration (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (compactification Y d)).obj (coefficient P Y d) ⟶ unit (AffineLinePurity.Ring P) Y :=
  letI := (projection_geometry Y d).2
  realizeTrace (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d) (compactification Y d)
    (etaleCoefficient P Y d) (coefficient_plus P Y d) (ordinaryTrace P Y aY d)
```

## New

The unrestricted coefficient_plus declaration is removed. The existing proved theorem is
public with its original statement and proof:

```lean
theorem coefficient_plus_on_base (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    DerivedCategory.TStructure.t.plus (etaleCoefficient P Y d) := by
  let T := iteratedAffineLine Y d
  have hT := affineTracePullbackInvertible (exponent P)
    (iteratedAffineLineProj Y d) (exponentUnit P Y aY)
  have h : ∀ n, DerivedCategory.TStructure.t.plus
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) T n) := by
    intro n
    induction n with
    | zero =>
      change DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit _ T)
      exact ⟨0, inferInstance⟩
    | succ n ih =>
      exact tensorLine_plus _ _ (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        _ T hT _ ih
  exact h d
```

The integration definition is:

```lean
def integration (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (compactification Y d)).obj (coefficient P Y d) ⟶ unit (AffineLinePurity.Ring P) Y :=
  letI := (projection_geometry Y d).2
  realizeTrace (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d) (compactification Y d)
    (etaleCoefficient P Y d) (coefficient_plus_on_base P Y aY d) (ordinaryTrace P Y aY d)
```

Its boundedness proof is now `(coefficient_plus_on_base P Y aY d)`. This changes only a
proof argument, and hence leaves the integration morphism definitionally equal by proof
irrelevance. The DAG's main statement, ordinary coefficients, ordered trace, source
comparisons, augmentation and exceptional transpose constructions are unchanged.
The Challenge declarations keep their types and mathematical meanings. The edited
public definition is submitted for the standard definition-meaning review of its
affected targets; proof irrelevance establishes that its morphism has not changed.

## Users

`tools/downstream.py Sheaf.Paper.AffineOrderedIntegrationTransposes --uses AlgebraicGeometry.ProEtale.AffineOrderedIntegration.coefficient_plus` reports 101
transitive importers and only the item itself as a textual user. No external
consumer requires adaptation. The full importer census follows.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineOrderedIntegrationTransposes | C1 | The sole caller integration uses the proved base-specific bound. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncSquare | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | A3 | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | X3 | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | H3 | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No reference to coefficient_plus; the canonical constructions and equation are unchanged. |

## Status

landed 20261026T001039-L-4164802 2026-10-26 (merge of deliver/C1/Sheaf.Paper.AffineOrderedIntegrationTransposes)

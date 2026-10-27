# AlgebraicGeometry.Etale.SfP1Transport.trace

## Reason

The original expanded trace formula causes repeated kernel normalization of the
concrete shifted Tate line when used in the generic trace-pasting calculation.
A standalone definitional expansion exceeded 120 seconds; diagnostics with a
lower heartbeat budget localized the expensive conversion to this formula.
The repair factors its coefficient-independent portion at an arbitrary complex and packages the ordered trace composition in the polymorphic traceComposite construction.
The proved presentationTrace_assoc equation expands the named comparison to
the original two maps, followed by any chosen arrow. Associativity proves
that the new formula is the original one. No existing signature, attribute or instance
changes. The previous delivery incorrectly claimed no public import change while its
stale base omitted A4's public import of SfP1SupportedExtMapData. This repair restores
that import and removes the duplicate supportedMap. The existing declaration remains
in SfP1SupportedExtMapData; the data node preserves its statement dependency on
 def-sf-p1-supported-ext-map-data and the current declaration attachments.
The affected existing module is unclaimed in the current claim records.

## Old

```lean
/-- Transport the given ordinary trace through the isomorphism over the base. -/
@[irreducible]
def trace (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) S :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward A f).map
      (ordinaryFiniteShiftedLinePullback A N hA t i.hom
        (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv ≫
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi).inv.app
        ((ordinaryFinitePullback A i.hom).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
      ((pushPull A i).hom.app
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫ τ ≫ (constantUnit A S).hom
```

## New

```lean
/-- A trace transported through forget-supports and an inverse line comparison.
Source: the ordered factors of the explicit projective-line trace construction.
Keeping the categorical composition polymorphic prevents repeated normalization
of its concrete shifted coefficient objects.
(blueprint: def-sf-p1-integral-transport-data). -/
@[irreducible]
def traceComposite
    {D E : Type*} [Category D] [Category E]
    (T T₀ : D ⥤ E) (z : T ≅ T₀) {B B' : D} (l : B ≅ B')
    {H J J' : E} (g : T₀.obj B ⟶ H) (τ : H ⟶ J) (u : J ⟶ J') :
    T.obj B' ⟶ J' :=
  z.hom.app B' ≫ T₀.map l.inv ≫ g ≫ τ ≫ u

/-- Direct-image composition and inverse-image/direct-image cancellation along i.
Source: the explicit trace construction, before the final trace arrow is inserted.
(blueprint: def-sf-p1-integral-transport-data). -/
@[irreducible]
def presentationTrace (B : DerivedCategoryModule A (ProjectiveLine S)) :
    (ordinaryFinitePushforward A f).obj ((ordinaryFinitePullback A i.hom).obj B) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B :=
  (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi).inv.app
        ((ordinaryFinitePullback A i.hom).obj B) ≫
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
      ((pushPull A i).hom.app B)

omit [Finite A] [IsProper f] in
/-- The named comparison retains the original order of direct-image factors.
Source: the explicit trace formula and associativity of composition.
Proof: unfold the two-factor comparison and reassociate with the final arrow.
(blueprint: def-sf-p1-integral-transport-data). -/
theorem presentationTrace_assoc
    (B : DerivedCategoryModule A (ProjectiveLine S))
    {K : DerivedCategoryModule A S}
    (τ : (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B ⟶ K) :
    presentationTrace A f i hi B ≫ τ =
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi).inv.app
          ((ordinaryFinitePullback A i.hom).obj B) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
          ((pushPull A i).hom.app B) ≫ τ := by
  unfold presentationTrace
  exact Category.assoc _ _ _

/-- Transport the given ordinary trace through the isomorphism over the base. -/
@[irreducible]
def trace (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) S :=
  traceComposite
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (ordinaryFinitePushforward A f)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f)
    (ordinaryFiniteShiftedLinePullback A N hA t i.hom
      (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS))
    (presentationTrace A f i hi
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    τ (constantUnit A S).hom
```

## Users

Current main has nine direct importers, found by scanning its import declarations.
All nine are checked against the repair, together with ProjectiveLineTraceAdjunction
and the item's parent. ProjectiveLineTraceNormalization needs a forced proof adaptation;
its signatures and public imports stay unchanged. The unrestricted --uses trace scan
also finds unrelated declarations with the same final name; those textual hits are
listed separately below (117 modules in the current scan). No downstream statement becomes weaker or stronger.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransportData | unclaimed | Add the real presentationTrace and traceComposite constructions and the proved associativity equation; factor trace through them. |
| Sheaf.AlgebraicGeometry.SfP1ChartMapComposition | unclaimed in current records | Signature and proof unchanged; compile against the repair. |
| Sheaf.AlgebraicGeometry.SfP1ChartExchange | unclaimed in current records | Signature and proof unchanged; compile against the repair. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison | unclaimed in current records | Signature and proof unchanged; compile against the repair. |
| Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison | unclaimed in current records | Signature and proof unchanged; compile against the repair. |
| Sheaf.SixFunctors.ProjectiveLineTraceRawAdjustment | unclaimed in current records | Unchanged direct importer; compile against the repair. |
| Sheaf.SixFunctors.ProjectiveLinePresentedKernelAdjunction | unclaimed in current records | Unchanged direct importer; compile against the repair. |
| Sheaf.SixFunctors.ProjectiveLinePresentedKernelIntegrals | unclaimed in current records | Unchanged direct importer; compile against the repair. |
| Sheaf.SixFunctors.ProjectiveLinePresentedIntegrals | unclaimed in current records | Unchanged direct importer; compile against the repair. |
| Sheaf.SixFunctors.ProjectiveLineTraceNormalization | unclaimed | Forced private tactic and proof adaptation; see sf-p1-trace-normalization-adaptation.md. |
| Sheaf.SixFunctors.ProjectiveLineTraceAdjunction | not consulted (unchanged) | Downstream normalization consumer; compile against the repair. |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue | E1 | Use the factored trace in the combining proof. |
| Sheaf.AlgebraicGeometry.SfP1PresentationExchange | E1, new | State geometric exchange using the coefficient-independent comparison. |
| Sheaf.AlgebraicGeometry.SfP1CoordinateLineComparison | E1, new | Unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.SfP1TraceTransportPasting | E1, new | Generic pasting takes the named geometric comparison as its argument. |
| Sheaf.AlgebraicGeometry.SfP1ConstantUnitNormalization | E1, new | Proved unit-normalization consumer; compiled unchanged against the factored trace. |
| Sheaf.AlgebraicGeometry.SfP1CachedRightUnitNormalization | E1, new | Proved unit-normalization consumer; compiled unchanged against the factored trace. |
| Sheaf.AlgebraicGeometry.SfP1ConstantUnitPullback | E1, new | Proved unit-normalization consumer; compiled unchanged against the factored trace. |

Repair validation compiled all 19 distinct modules successfully: the nine packet modules,
the nine current direct importers, ProjectiveLineTraceAdjunction and the parent
SfP1ProjectionTraceTransport (normalization is both a packet module and direct importer).
The ten unchanged validation copies were removed before delivery.

Additional textual hits from the unrestricted scan:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransport | not consulted (unchanged) | Uses datum_trace to identify the same constructed trace; no unfolding or signature change. |
| Sheaf.Paper.AdicUnitTraceScalarData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTraceLimitWitnessExistence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTracePresentationExistence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.DiagonalTraceResultExistence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.EvenTensorPositivity | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FiniteTraceDiagonalDatum | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FourierAdicCharacterOf | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.GeometricOperations | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Data | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerClassProjective | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerP1EtaleEpsilon | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerP1TriangleWords | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SecSmoothPurity.TransportAffineNormalization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SecSmoothPurity.TransportCompatibility | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SecSmoothPurity.TransportGeometry | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SecSmoothPurity.TransportScalarCompatibility | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.Targets.PoincareUncurry | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| Sheaf.TraceFormula.CondensedStalkFrobeniusOrbitTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TraceScalarExtension | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.Main | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.LSeries | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunction | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not consulted (unchanged) | Textual hit for another trace declaration or field; no adaptation. |

Challenge.lean and every target signature are unchanged. If stage-2 review
tracks trace as a definition used by a target statement, that review is reopened;
presentationTrace_assoc supplies the equality with the old construction.
| Sheaf.Paper.DiagonalTraceFiniteIntegralProjection | not consulted (unchanged) | Textual trace hit; no signature change or adaptation. |

## Status

landed 20261027T054555-L-964137 2026-10-27 (merge of deliver/E1/Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue)

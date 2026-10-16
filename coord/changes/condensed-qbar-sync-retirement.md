# AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper

## Reason

The 2026-10-17 upstream synchronization reintroduced an ambient all-unbounded instance that was
retired by the reviewed F3 delivery (see the landed `condensed-qbar-bounded-push.md` record).
Its proof is `sorry`; its existing dispute comment explains that the supplied coproduct
continuity argument only covers bounded-below inputs. No counterexample to this exact internal
condensed coefficient instance is claimed. This repair restores the previously reviewed public
interface, keeping the bounded-below component theorem unchanged. It does not prove or silently
weaken the retired statement. The anonymous Omega Shriek example is also retired because it
requires the ambient instance. The finite-extension Shriek example remains unchanged.

No definition or target statement changes. Current bounded constructible consumers already
extract a lower bound and use the retained component theorem; no consumer adaptation is needed.
The imported blueprint node `lem-sfb-qlbar-push-iso-proper` remains an unresolved blueprint
assertion; it is not claimed proved or deleted from the DAG by this restoration.

## Old

```lean
instance isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper [IsProper f]
    (E : FiniteIntermediateField ℓ) :
    IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) :=
  sorry
```

## New

The declaration and the dependent anonymous Omega Shriek example are removed. The separately
named bounded-below component theorem, all finite-extension results, and all definitions and
retained signatures remain unchanged.

## Users

`tools/downstream.py` reports 103 downstream modules and one explicit use of the retired name,
in the item itself. A source-wide search likewise finds no consumer naming it. The bounded
constructible consumer explicitly applies
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`. Current holders are recorded
below; no held consumer is modified.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | D2 | Retire disputed ambient instance and its anonymous Omega Shriek example. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | C1 | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | F2 | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No signature or definition change; no explicit use of retired instance. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No signature or definition change; no explicit use of retired instance. |
| TargetsCheck | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.TraceFormula.Main | unclaimed | No signature or definition change; no explicit use of retired instance. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No signature or definition change; no explicit use of retired instance. |

## Status

landed 20261016T221603-L-1612718 2026-10-16 (merge of deliver/D2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)

# AlgebraicGeometry.ProEtale.RationalP1.pullSectionIso

## Reason

Specializing PullSectionCompatibility.mk with the published section equation makes
kernel checking unfold the exposed composite pullSectionIso, including derived
composition and equality transports. The original two-line proof exceeded 120 seconds.
Marking this actual construction no_expose keeps the same map while treating it as
abstract in importers. A proved pullSectionIso_eq exposes precisely its original
construction when a proof needs it. The repaired item compiles in 7.2 seconds in the full compatibility check.
No target signature or mathematical definition changes. No data is chosen from a theorem.

The definition module was unclaimed on the server. Every existing consumer signature,
visibility and proof is preserved. Seven consumers need a forced one-line removal of
the local irreducible attribute, because an unexposed imported body no longer admits
that attribute. Original failures were compiled and recorded in the worker report.

## Old

```lean
def pullSectionIso (Y : Scheme.{u}) (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    CondensedRing.moduleObjectDerivedPullback Λ f ⋙
      CondensedRing.moduleObjectDerivedPullback Λ (diagonalImmersion Y) ≅
        𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) :=
  (CondensedRing.leftDerivedUpperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
    eqToIso (congrArg (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h) ≪≫
      CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y)
```

## New

```lean
@[no_expose]
def pullSectionIso (Y : Scheme.{u}) (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    CondensedRing.moduleObjectDerivedPullback Λ f ⋙
      CondensedRing.moduleObjectDerivedPullback Λ (diagonalImmersion Y) ≅
        𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) :=
  (CondensedRing.leftDerivedUpperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
    eqToIso (congrArg (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h) ≪≫
      CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y)

/-- The canonical section comparison is the pullback compositor followed by the
identity comparison. This equation keeps the construction available without unfolding
it during unrelated dependent interface checks. Source: blueprint unit/counit clause 1
(blueprint: def-sfb-projective-diagonal-pullback). -/
theorem pullSectionIso_eq (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    pullSectionIso Λ Y f h =
      (CondensedRing.leftDerivedUpperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
        eqToIso (congrArg (fun g ↦ CondensedRing.moduleObjectDerivedPullback Λ g) h) ≪≫
          CondensedRing.leftDerivedUpperStarId Λ (ProjectiveLine Y) := by
  unfold pullSectionIso
  rfl
```

## Users

The table lists all 82 downstream modules reported by downstream.py, including all
15 modules mentioning pullSectionIso, plus its defining module. The holder snapshot
is informational for untouched modules; adapted holders were checked on the server.
All ten direct importers and all other modules mentioning the changed name are compiled
against the repaired definition. Unchanged compatibility-check copies are removed from
the delivery after validation. All 21 compatibility files passed, with no warnings and every file
under 60 seconds; the slowest fresh check took 34.5 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineLineAdjunctionAssembly | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.CanonicalSectionProjectionCore | unclaimed in shared snapshot | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.CanonicalSectionProjectionCoreCoherence | Y8 (checked on server) | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.CanonicalSectionProjectionTransport | unclaimed in shared snapshot | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.DiagonalCompletedChernSplitting | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.ProjectiveCanonicalSectionProjection | unclaimed in shared snapshot | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed in shared snapshot | Same canonical construction; hide body and add proved equation. |
| Sheaf.Paper.ProjectiveNormalizedUnitCounitRestriction | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.ProjectiveSupportedSectionProjection | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.ProjectiveSupportedSourceArrow | S5 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.ProjectiveSupportedSourceNormalization | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalExceptionalInverseImageExistence | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1AmbientTail | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1CounitInversionCondition | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1FirstAmbientContraction | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1FirstTraceTransport | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1FirstTraceTransportCore | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1FirstTraceTransportCounit | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded | S6 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1LineFromPreservation | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1LocalizingPreservation | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1LocalizingProjection | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1PositiveLineConstructible | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ProjectionNaturality | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1RestrictionExactness | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernBaseChange | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernBaseChangeChern | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone | W8 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernBaseChangeChernSome | W9 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernBaseChangeUnit | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernDegree | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernMaps | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernP2Degree | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernP2Splitting | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernQDegree | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion | D2 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernQLeftInverse | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernQRightInverse | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernQSplitting | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1ScalarChernSplittings | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondAmbientContraction | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor | unclaimed in shared snapshot | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.RationalP1SecondExchangeProjection | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondExchangeProjectionNative | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondPretrace | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondPretraceData | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondProjectionInterchange | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondProjectionInterchangeCore | X5 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondProjectionInterchangeTail | X6 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondPullComparison | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondPullComparisonExpansion | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondPullSection | N2 | Fill both proofs and remove obsolete local attribute. |
| Sheaf.Paper.RationalP1SecondPullSectionCoreComm | unclaimed in shared snapshot | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.RationalP1SecondPullSectionFinalTransport | unclaimed in shared snapshot | Remove only pullSectionIso from local irreducible attribute. |
| Sheaf.Paper.RationalP1SecondPullSectionTransportData | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondPullSectionTransportSpecialized | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondScalarTrace | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondTraceEquation | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SecondTraceReordering | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1SectionEvaluation | K4 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1TensorShiftNaturality | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1Triangle | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1UnitFactorization | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalP1UnitInversionCondition | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RationalTatePullback | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.RestrictionLocal | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.ScalarP1UnitMateComponent | A5 | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Paper.TateTwistedProjection | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in shared snapshot | Source unchanged; no statement or definition changes; uses the same canonical map. |

## Status

landed 20261028T020608-L-2527929 2026-10-28 (merge of deliver/N2/Sheaf.Paper.RationalP1SecondPullSection)

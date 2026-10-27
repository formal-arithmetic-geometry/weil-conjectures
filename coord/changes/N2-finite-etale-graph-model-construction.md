# AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.graphSupportModel

## Reason

Construct the canonical graph isomorphism directly rather than selecting its uniquely
normalized representative from `etaleSupportMapCompatibility`. The public signature and
intended map are unchanged. The existing graph construction has the same sheaf graph
normalization and homotopy-descent formula: graph extension is unique after composing
with the monic compact-support inclusion, and localization determines the derived map.
The selected-witness uniqueness conversion caused kernel checking to exceed 60 seconds.
The direct construction makes the identification with the canonical graph comparison
reflexive, without changing any target signature or choosing an arbitrary object.
Any target that unfolds this definition should receive the normal independent definition
review again; this record does not assert that the Lean comparator alone checks its meaning.

## Old

```lean
def graphSupportModel (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (Etale.etaleSupportMapCompatibility A).choose_spec.choose
```

## New

```lean
def graphSupportModel (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  fun e _ _ _ _ c ↦ Etale.canonicalEtaleCompactSupportComparison A e c
```

## Users

`tools/downstream.py ... --uses graphSupportModel` reports only the item itself as a
textual user and 36 transitive importers. No other source uses the definition directly.
The table includes the item and all transitive consumers for review.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | N2 | Canonical graph construction; complete normalization proof. |
| `Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | X2 | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceSquare` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartDncSquare` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartEpsilonPasting` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartExceptionalCounitEquation` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartExceptionalMateCoherence` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartNormalIntegrationSquare` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ChartTargetOpenDescent` | X3 | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDescent` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.DifferenceCoordinateSectionIdentifications` | Y7 | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.DoubleDiagonalSectionIdentifications` | X2 | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.DualizingCocycleSourceEtale` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.DualizingPrimitiveOpenRestriction` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.DualizingSigmaCocycleLocality` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.EtaleCartesianTowerTensorComparison` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.GeneralChartComparisons` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ModelAffineIntegrationOrientation` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ModelChartOrientationAssembly` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ModelOrientationChartDescent` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ModelOrientationSourceNaturality` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.ModelOrientationTateDetection` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PurityCompositionCompatibleDncCharts` | T2 | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionBaseComparisonLaws` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionEtaleRestriction` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionFibreSquares` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionNormalizedSpecialization` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionRestrictionData` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.Paper.SectionDncIntegrationSquare` | N3 | No direct use; signature and intended map unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | No direct use; signature and intended map unchanged; no adaptation. |

## Status

landed 20261025T202632-L-2736248 2026-10-25 (merge of deliver/N2/Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization)

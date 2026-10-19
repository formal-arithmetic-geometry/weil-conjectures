# finiteCoefficientModulePullback_tensor

## Reason

Complete the commutative tensor comparison by comparing adjunctions to the same
specified direct image. All existing public signatures, visibility, attributes and
data definitions are unchanged. The checker records two scoped commands around
proved private helpers as an interface change, so this record documents their scope.
There are no consumer adaptations and no change to any target's meaning or type.

## Old

The public signature, with proof `sorry`:

```lean
theorem finiteCoefficientModulePullback_tensor :
    Nonempty
      (finiteCoefficientModulePullback f Λ ⋙
          SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ U) ≅
        SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ V) ⋙
          Scheme.proEtaleRingModulePullback f
            (finiteCoefficientCommRing Λ V) (finiteCoefficientCommRing Λ U)
            (asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of Λ))))
```

The existing instance registration was followed immediately by the theorem.

## New

The identical public signature, now with a complete proof:

```lean
theorem finiteCoefficientModulePullback_tensor :
    Nonempty
      (finiteCoefficientModulePullback f Λ ⋙
          SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ U) ≅
        SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ V) ⋙
          Scheme.proEtaleRingModulePullback f
            (finiteCoefficientCommRing Λ V) (finiteCoefficientCommRing Λ U)
            (asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of Λ))))
```

Between the existing instance registration and the theorem, a `section` contains
only proved private helpers. It opens `Scheme` locally and ends before the public
theorem. The command `omit [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] in`
applies only to private theorem `finiteTensorForgetUnit`. Declaration-local backward
elaboration options likewise affect only private helpers or the final proof.
The added import `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
is proof-only. Importers see the same existing interface and constructions.

## Users

No consumer is edited. Every direct importer below retains its public interface;
its ownership is irrelevant because this delivery changes none of its lines.
The read-only downstream check for `finiteCoefficientModulePullback_tensor` is also
run; the theorem's statement and visibility remain identical for all users.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleConstantExact | P2 | One proof completed; scoped private helpers added. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientOpenKInjective | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientOpenRestriction | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedSupportAdjunction | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleUnderlying | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenDerivedImage | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ProEtalePairFlasque | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not adapted | Existing interface unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SupportLocalizationTriangle | not adapted | Existing interface unchanged; no edit. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.ClosedSupportedCupVanishing | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.CompactSupportPerfectness | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.CompletedExtensionZeroComparison | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.ConcentratedComplexShift | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.ConstructiblePullbackTExact | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.DerivedPullbackTensorIso | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.ExplicitExceptionalPreservation | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralCoherenceTower | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralDerivedOperations | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralOperationsScalarExtension | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralOperationsWellDefined | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.IntegralPullbackComposition | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.PullbackTorAmplitude | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.PurityFiniteKummerLevel | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.PurityGeneralAdmissibility | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.StratumScalarExtension | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.SupportedHomPullback | not adapted | Existing interface unchanged; no edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Existing interface unchanged; no edit. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not adapted | Existing interface unchanged; no edit. |
| Sheaf.SixFunctors.SchemeGaloisComparison | not adapted | Existing interface unchanged; no edit. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not adapted | Existing interface unchanged; no edit. |
| Sheaf.TraceFormula.PointTransportComposition | not adapted | Existing interface unchanged; no edit. |

## Status

landed 20261019T112505-L-3946307 2026-10-19 (merge of deliver/P2/Sheaf.AlgebraicGeometry.ProEtaleConstantExact)

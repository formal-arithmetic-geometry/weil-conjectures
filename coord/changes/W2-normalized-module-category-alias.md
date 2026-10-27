# normalizedDVRModules and normalizedDVRModuleRes

## Reason

The normalized tower and scalar-extension interfaces used different names for
exactly the same module category. Share scalarReductionTarget. Keep the original
quotient-restriction construction as a reducible ordinary definition so the kernel
compares its named head before expanding finite coefficient actions. An explicit
proved additivity instance exposes its existing structure. The module is unclaimed;
its new public import supplies the scalar-reduction interface.

## Old

```lean
abbrev normalizedDVRModules (n : ℕ) :=
  CategoryTheory.ringedSiteModules.{max u (t + 1)} (integralCoefficientSheaf l E X n)
```

```lean
noncomputable abbrev normalizedDVRModuleRes {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModules l E X n ⥤ normalizedDVRModules l E X m :=
  SheafOfModules.restrictScalars (normalizedDVRQuotient l E X h)
```

## New

```lean
abbrev normalizedDVRModules (n : ℕ) :=
  scalarReductionTarget l E X n
```

```lean
@[reducible]
noncomputable def normalizedDVRModuleRes {m n : ℕ} (h : n ≤ m) :
    scalarReductionTarget l E X n ⥤ scalarReductionTarget l E X m :=
  SheafOfModules.restrictScalars (normalizedDVRQuotient l E X h)
```

```lean
instance normalizedDVRModuleRes_additive {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRModuleRes l E X h).Additive := by
  unfold normalizedDVRModuleRes
  infer_instance
```

The restriction construction body is verbatim; the two endpoint category names
are definitionally equal. No action, quotient or mathematical statement changes.
The explicit additive instance is attached to the existing definition node.
Definition-sensitive review is requested for reached targets using these definitions.
The earlier five interface identity checks, including the category alias, compile
by rfl (19.3 seconds); the restriction bodies are also syntactically unchanged.

The derived-category alias `normalizedDVRDerived` also retains its original body
as a reducible ordinary definition instead of an abbreviation:

```lean
@[reducible]
noncomputable def normalizedDVRDerived (n : ℕ) :=
  @DerivedCategory (normalizedDVRModules l E X n) _ _ (HasDerivedCategory.standard _)
```

Its data and standard localization instance are unchanged.

The legacy interfaces `normalizedDVRRes`, `normalizedDVRDerivedTowers`,
`normalizedDVRResCompleted` and `normalizedDVRTowerEvaluation` also change from
`noncomputable abbrev` to `@[reducible] noncomputable def`. Their signatures and
construction bodies are verbatim. This keeps the completed-module restriction,
standard localizations and derived evaluation behind named interfaces.

## Users

Source scan refreshed 2026-10-26T08:59+00:00.
The import closure has 1726 modules; 58 mention the changed
declarations under the `tools/downstream.py --uses` criterion.
Statements, module actions and constructions remain definitionally equal.
No forced consumer edits are included.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.NormalizedDVRTowerEvaluationFull` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.AdicRoosRealizationReductions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | J6 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefOpenTensorEvaluationData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionOrdinaryQuotientIso` | Y2 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionRestrictedTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionStrictRepresentatives` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientExtensionStrictTensorNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientRingedSequenceSite` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CoefficientSequenceRoosModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompactSupportCoefficientTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedCoefficientCompletionRoosTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | E4 | definitionally identical data; no adaptation |
| `Sheaf.Paper.CompletionUnitModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteCounitRestrictionTowers` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.FinitePullbackTensorComparison` | U5 | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionRestrictionCoherence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTransitionCocycles` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralReductionTransitions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralScalarTowerEffectivity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.IntegralStrictReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedArithmeticInterpolation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRAdicConeModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRBoundedFreeCone` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVREffectivity` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRFlatCokernel` | W6 | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRKFlatReductionModel` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRKFlatTransition` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRRoosAugmentation` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRRoosFiniteReduction` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRScalarCokernelComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRStrictCoefficientAdjoint` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedDVRTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.NormalizedTensorConstraintTransport` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PairingCoefficientUnit` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointFibreDerivedTensorFiniteModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PointFibreDerivedTensorScalar` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceAdjointResolutionData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.PurSequenceKFlatComparisonData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionKFlatModels` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionKFlatNormalization` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionKFlatOperations` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.QuotientExpressionStrictKFlatTowers` | N3 | definitionally identical data; no adaptation |
| `Sheaf.Paper.StrictQuotientExpressions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionPullbackNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.Paper.TransportedReductionScalarNormalized` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionDefinitions` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.OpenSemilinearTensorModelData` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.AutomorphismTensorReductionComparison` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | definitionally identical data; no adaptation |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | definitionally identical data; no adaptation |

## Status

landed 20261026T102415-L-355579 2026-10-26 (merge of deliver/W2/Sheaf.Paper.IntegralOperationRoosEffectivity)

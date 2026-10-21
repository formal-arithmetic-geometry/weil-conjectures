# SemilinearProperOpen evaluation proof-local commands

## Reason

Server preflight classifies changes to commands such as `universe`, scoped `open`,
and local `attribute` as potential interface changes. The new private generic
exact-localization helpers need universe parameters and short names for the exact
open adjunction. Composite exact functors need the two composition instances.
These commands occur in the existing `Evaluation` section and do not change any
exported attribute or declaration signature. This record documents their scope
and every downstream module despite the absence of a semantic interface change.

## Old

There were no corresponding commands between `evalP` and `evalR`. The two public
statements, verbatim, were:

```lean
theorem evalR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (evalR C τ n f) := by
  sorry

theorem evalJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (evalJInv C τ n j) := by
  sorry
```

## New

Both public statements are identical, with complete proofs replacing their
`sorry` bodies. The added commands, verbatim, are:

```lean
universe v h w

open SheafOfModules.OpenTensorNormalization in
```

The scoped `open ... in` applies only to the immediately following private theorem
(`exact_hom_fac` or `exact_inverse_mate_isIso`). The following command occurs before
`exact_inverse_mate_isIso` and again before `constant_open_inverse_mate_isIso`:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The instance attributes are local to the existing `Evaluation` section and expire
at `end Evaluation`. The added universes are used only by new private helpers.
The scoped transparency and heartbeat options also apply only to private proofs.
All existing definitions, instances, theorem signatures, and public imports stay
verbatim. Target statements and their meanings are unchanged. No consumer needs
adaptation.

## Users

The read-only downstream scan reports 37 downstream modules. The declaration-use
scans for `evalR_isIso` and `evalJInv_isIso` report only the item itself. Every
module is listed below for completeness; none is edited by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | U4 | Proof-local commands support the two new proofs; no signature change. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Unaffected: all public signatures, definitions and exported attributes are unchanged. |

## Status

landed 20261021T061713-L-1815513 2026-10-21 (merge of deliver/U4/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)

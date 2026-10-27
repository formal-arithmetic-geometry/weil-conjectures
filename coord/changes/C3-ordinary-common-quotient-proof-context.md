# Sheaf.Paper.OrdinaryCommonQuotientTower proof context

## Reason

Complete the original existence theorem. Static preflight requests a record for
added scope and elaboration commands. Every existing public signature, public
import, and public definition body is unchanged. All added helpers are private
and completely proved. No target statement or definition changes meaning, and
no consumer adaptation is required.

## Old

The original scope opening is:

```lean
open scoped ChangeOfRings
```

The original file already has `set_option backward.isDefEq.respectTransparency false`.
It has no `RingPushout` section or private pushout/comparison/transition helpers.
The original theorem signature, retained verbatim, is:

```lean
theorem nonempty_ordinaryCommonQuotientTower :
    Nonempty (OrdinaryCommonQuotientTower D a b)
```

Its proof was `by sorry`.

## New

The scope opening becomes:

```lean
open scoped ChangeOfRings TensorProduct
```

The additional elaboration option is scoped inside the new `RingPushout` section:

```lean
set_option backward.isDefEq.respectTransparency.types false
```

The fully proved private helpers are enclosed in `section RingPushout` /
`end RingPushout`. Their `omit ... in` commands remove unused automatically
included hypotheses only from those new private lemmas. The original variables,
notations, options, attributes, and namespace remain in place. After proving the transition's section API, the helper section also contains:

```lean
attribute [local irreducible] rawTransition
```

This prevents later transport proofs from unfolding the large private
adjunction construction. The attribute and the transparency option end with the
helper section, before the unchanged public tower declaration. Profiling found
that their earlier file-wide scope caused unnecessary type checking and linting.
The scoped version compiled in 24.1 seconds during profiling.

No global instance
or attribute is added. The tensor scope, transparency option, section, and omit
commands affect elaboration of this file; they export no changed declaration or
instance to importing files. The proof-only imports expose the existing ordinary
adjunction, normalization, and comparison inside this file only.

The existing theorem above now has a complete proof. The existing structure,
unit definitions, and all previously proved theorem signatures and bodies are
unchanged. The node's mathematical statement is unchanged.

## Users

The following are the modules reported by `tools/downstream.py` (including the
item's direct declaration occurrence). None needs adaptation: the entire public
interface and every existing public definition body are identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedFiniteComparisonModels | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedFiniteScalarExchange | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedOpenFiniteEtaleOrigins | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedStrictOpenExchange | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteQuotientOrdinaryComparison | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteQuotientTransitionCompatibility | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FlatCommonQuotientReductionTower | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | claimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RingedCommonQuotientPullbackComparison | claimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCommonQuotientTower | C3 | Existing interface unchanged; no adaptation. |

The direct external declaration user is
`Sheaf.Paper.FlatCommonQuotientReductionTower`; its call uses the same theorem
with precisely the same parameters and conclusion. The other downstream modules
retain their imports and interfaces. No source-library module is changed.

## Status

landed 20261022T113851-L-336679 2026-10-22 (merge of deliver/C3/Sheaf.Paper.OrdinaryCommonQuotientTower)

# Sheaf.Paper.PrincipalReductionConeCalculus proof context

## Reason

The strict scalar-cone calculus needs generic private helpers for coherent shifts,
cone interchange and their equations. The module-command checker flags the additional
section variables, namespace-local opens, elaboration options and local attributes as
an interface change. This record documents those commands. All eight existing public
signatures and all existing public imports are verbatim. No target statement or
public definition changes its meaning. No source-library module is changed.

## Old

The existing module had the following elaboration options:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
```

There were no `PrincipalConeShift` or `StrictCones` helper blocks, and no local
scalar-action opacity attribute. The primary theorem had a `sorry` body.

## New

The existing options are retained, with these additions for the private proof API:

```lean
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

`PrincipalConeShift` introduces variables and opens for its private cone/shift
constructions. The `StrictCones` section introduces generic abelian-category variables,
namespace-local `CochainComplex`, `HomComplex` and `Preadditive` opens, and a proved
`private local instance chainAction_commShift`. The local instance is confined to
that section. Every helper is private and has a complete proof or a concrete definition.
After proving the scalar multiplication law, the proof namespace contains:

```lean
attribute [local irreducible] DerivedNakayama.scalarOnModules uniformizerEnd
```

This prevents elaboration from expanding the scalar action through pullback and unitors;
it changes no definition body and ends at the enclosing namespace. The same-module
generic calculus lemma specializes to the original theorem. The three original tensor
proof imports are replaced by the separate normalized-comparison theorem's private import.
The two additional private imports provide sheaf tensor extensionality and the explicit
pointwise multiplication construction. Existing importers see the same public API.

## Users

The following table includes the item and every transitive downstream module returned
by `tools/downstream.py`; the only external textual use of the primary theorem is
`Sheaf.Paper.DerivedNakayamaFirstReduction`. No consumer needs adaptation because
existing signatures, visibility and public definitions are unchanged. Claim holders
are recorded at the time of this repair.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.PrincipalReductionConeCalculus` | Y2 | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.CompletionTriangleComparison` | F7 | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.DerivedNakayama` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralResidueClassTriangleClosure` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralStratumHomFormula` | K6 | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.QcqsIntegralFiniteModelCompleteness` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.QcqsProperConstructibleClosedBaseChange` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Existing statements, definitions and public imports unchanged; no adaptation needed. |

## Status

landed 20261021T204056-L-3935640 2026-10-21 (merge of deliver/Y2/Sheaf.Paper.PrincipalReductionConeCalculus)

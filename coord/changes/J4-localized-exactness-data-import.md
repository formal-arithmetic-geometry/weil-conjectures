# Sheaf.CategoryTheory.LocalizedModuleExactIndependent public import

## Reason

The stage-3 proof of `localBaseData_exists` needs the proved generic restriction
exactness and K-flat restriction APIs. Their import closure currently imports the
higher projection theorem back into its own construction:
`RingedProjectionLocalBaseData -> RingedSiteRestrictionKFlat ->
LocalizedModuleExactForSystems -> LocalizedModuleExactIndependent ->
RingedProjectionRestriction -> RingedProjectionLocalModel ->
RingedProjectionLocalData -> RingedProjectionLocalDerivedData ->
RingedProjectionLocalBaseData`.

`LocalizedModuleExactIndependent` only uses the `Mod`/derived-category vocabulary
from the lower data module. Replace the higher public import by its existing
public data import. All declaration signatures, bodies, attributes and other
imports in this unclaimed Sheaf module remain verbatim. The removed module adds
only `ringedProjectionRestriction` to its public data import; the downstream use
search reports zero uses of that theorem. All 17 original direct importers are checked
against the narrowed import. Fifteen compile unchanged; two original files exceed
the limit even before the repair and are split without changing their declarations
or proof bodies, as recorded in `J4-localized-exactness-consumer-split.md`. No target definition or statement changes,
and no source-tree declaration is removed or edited.

## Old

```lean
public import Sheaf.Paper.RingedProjectionRestriction
```

## New

```lean
public import Sheaf.Paper.RingedProjectionRestrictionData
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenSlicePresentation | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.CategoryTheory.LocalizedModuleExactForSystems | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Split the proved construction portion to satisfy the per-file limit; preserve all declarations. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.OpenImmersionTensorPiece | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Split the proved construction portion to satisfy the per-file limit; preserve all declarations. |
| Sheaf.Paper.StrictTowerRealizationComparisons | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.SecSmoothPurity.LocalizedExtensionZeroLinearDerived | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.SixFunctors.ConstantOpenRestrictionModelComparison | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.SixFunctors.OpenFactorCoherenceData | unclaimed | Compile unchanged against the narrowed import. |
| Sheaf.Paper.RingedProjectionLocalBaseData | J4 | Its new proof imports the generic exactness APIs without a cycle. |

## Status

landed 20261027T131459-L-2941620 2026-10-27 (merge of deliver/J4/Sheaf.Paper.RingedProjectionLocalBaseData)

# Completed-pullback private import cycle

## Reason

The remaining membership theorem in `Sheaf.Paper.PbcQbarCompletedPullback` follows
its documented finite-reduction argument using the already proved
`pbc_constructible_reduction_pullback`. The latter imports `SbcCompletedOperations`,
which imports `CompletedPullbackReduction`. Both auxiliary modules had private
imports of `PbcQbarCompletedPullback`, although neither mentions any declaration
of that module. Removing these two back-edges permits the required proof import.
All public imports, declarations, signatures, attributes and definitions are preserved.
No adopted source-library module is edited.

The auxiliary modules are unclaimed in the shared claim records. Their public
interfaces and theorem proofs are unchanged. The replacement prerequisite import
supplies `pbcFiniteStageAbSheafify` and `pbcFiniteStageAbLocallyBijective`,
the priority-3000 instances in the required PBC coefficient universe. They were
previously reached through the Qbar application. Without this context, the
existing `sbcOrdinaryModuleIso_naturality` proof reports an unresolved universe
constraint in the locally-bijective criterion. The direct instance import preserves this required context in both modules.

## Old

In each of `Sheaf.Paper.CompletedPullbackReduction` and
`Sheaf.Paper.SbcCompletedOperations`:

```lean
import Sheaf.Paper.PbcQbarCompletedPullback
```

## New

In both auxiliary modules the private application import is replaced by:

```lean
import Sheaf.Paper.PbcFiniteCompletedCoefficientMap
```

All other imports, theorem proofs and declaration bodies remain identical.

## Users

`tools/downstream.py` with `--direct --uses pbcQbarCompletedPull
pbcQbarIntegralPull_mem` finds fourteen direct importers of the two auxiliary modules
and zero uses of either removed dependency's declarations. The table includes those
importers and both adapted/item modules. Because only private imports change,
the importer-visible interface is identical; target meanings do not change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | Replace private application import by its finite-coefficient instance module. |
| Sheaf.Paper.PbcQbarCompletedPullback | M2 (this assignment) | Use the existing reduction-preservation theorem to close membership. |

## Status

landed 20261021T111321-L-73258 2026-10-21 (merge of deliver/M2/Sheaf.Paper.PbcQbarCompletedPullback)

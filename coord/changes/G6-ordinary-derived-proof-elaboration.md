# WeilConjectures.ordinaryIntegralPull_hasLeftDerived

## Reason

The proof imports generic scalar-extension and derived-functor interfaces. Their general
instances compete with the existing fixed-universe instances. Suppress three such instances
within the module and supply the actual pro-etale site size with a proved private instance.
This changes elaboration controls only; every public signature, definition body and public
import remains verbatim. The gate requests a change record for module attribute commands.

## Old

The assigned module contains the preamble:

```lean
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
```

## New

The same preamble now additionally contains:

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
attribute [-instance] WeilConjectures.scalarReductionTargetDerived
```

The only corresponding replacement instance is private and proved:

```lean
private instance ordinarySiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
```

The new private comparison data are marked irreducible to avoid reopening their adjunction
and natural-isomorphism construction during downstream proof elaboration:

```lean
@[irreducible] private def ordinaryTensorAdjunction
@[irreducible] private def ordinaryTensorPushIso
@[irreducible] private def ordinaryTensorPullIso
@[irreducible] private def ordinaryTensorHomotopyIso
```

These are private declarations added in this delivery, with fully proved bodies. They do not
change a public definition's transparency or data.

## Users

The downstream census lists 19 modules. The three closed theorem names have no textual
consumer outside the assigned module. All downstream modules retain exactly their original
public interfaces; none is adapted. Holders below are the current claim records at preparation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | G6 | Assigned proof changes only. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.ConstructibleProjectiveChartRefinement | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.FiniteProjectiveModelPullback | N2 | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | C7 | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.ProperIntegralOrdinaryInputs | Q5 | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.QcqsCompletionUnitLocality | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Unchanged signatures, public definition bodies and public imports; no adaptation. |
| Sheaf.Paper.RealizationCompletedMate | F6 | Unchanged signatures, public definition bodies and public imports; no adaptation. |

## Status

landed 20261023T231155-L-3556451 2026-10-23 (merge of deliver/G6/Sheaf.Paper.OrdinaryCompletedIntegralPullback)

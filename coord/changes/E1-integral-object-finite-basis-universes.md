# WeilConjectures.IntegralObjectQuotient.fixedSmall

## Reason

Restore the quarantined `Sheaf.Paper.IntegralObjectFiniteBasis` module recorded in
`coord/rework.tsv`. The archived file fails at the slice-basis binder with the constraint
`u + 1 =?= max (u + 1) ?u.31`. The imported `scalarReductionSiteSmall` instance leaves
an unrelated coefficient universe unresolved. Exclude it from this file's instance search,
using the existing fixed-size private instance, and specify every universe of its proof.
The normalized finite-basis construction and its theorem are preserved.

## Old

```lean
private instance (priority := 5000) fixedSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
```

The original file did not disable `WeilConjectures.scalarReductionSiteSmall`.

## New

```lean
private instance (priority := 5000) fixedSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
```

Add `WeilConjectures.scalarReductionSiteSmall` to the existing disabled-instance list.
All public signatures, definitions, imports, and the DAG attachment and proof route stay
as in the archived module. The private witness still proves the same proposition.
No target changes meaning and no target statement requires renewed semantic review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralObjectFiniteBasis` | E1 | restore and repair instance inference |
| `Sheaf.Paper.IntegralObjectPullbackQuotientBasis` | not recorded in local claims | quarantined direct importer; checked against restoration |

The source search included `lean/` and `quarantine/`; the sole direct importer is the
quarantined quotient-basis module. `tools/downstream.py` cannot index the item while its
source is quarantined and reports `unknown module(s)`; the explicit source search
therefore supplies the consumer inventory. The item and the unchanged quarantined
consumer compiled in import order in 43.3 and 43.5 seconds respectively. The temporary
consumer copy was removed after that check.

## Status

landed 20261026T111825-L-1743021 2026-10-26 (merge of deliver/E1/Sheaf.Paper.IntegralObjectFiniteBasis)

# AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonIso

## Reason

Restore the quarantined module assigned by coord/rework.tsv. Compiling the archive
reproduces `Invalid field IsAcyclicTensorKFlat` at its public theorem's hypothesis
`hP`. The public upstream stalk-transport module exposes the differently named
`IsKFlatTensor`. The existing `IsAcyclicTensorKFlat` definition is available only
through private proof imports, which cannot supply a public signature. Add its
existing defining module as a direct public import.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso
```

The declaration signature, docstring and proof are verbatim from quarantine.
This repairs visibility of its existing hypothesis without changing its meaning.
The restored module compiles through lcompile.py in 4.9 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso | E1 | Restored with the public import required by its signature. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison | quarantined; no current claim found | Its existing theorem application retains exactly the same signature; no adaptation. |

`tools/downstream.py --allow-missing --uses` reports no live downstream modules.
Searching lean/Sheaf and quarantine/Sheaf identifies the archived consumer above
as the only direct importer and external user. Its application at line 130 uses
the unchanged declaration. The analogous WeilConjectures modules use their own
upstream comparison and are unaffected. No target statement, definition, DAG
attachment, proof dependency or unit route changes. The quarantine is retained.

## Status

landed 20261020T152954-L-2857471 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso)

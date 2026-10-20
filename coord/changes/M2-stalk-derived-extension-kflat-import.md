# AlgebraicGeometry.SingleComplexBaseChange.stalkDerivedExtensionComparison_isIso

## Reason

Restore the quarantined item listed in `coord/rework.tsv`. Its archived original
fails with `Invalid field IsAcyclicTensorKFlat` in the public theorem signature.
The upstream stalk transport now exposes the predicate `IsKFlatTensor`, whereas
this theorem intentionally retains its existing `IsAcyclicTensorKFlat` hypothesis.
Import that hypothesis's existing definition explicitly and publicly.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
```

The entire theorem signature and proof are verbatim from the quarantine archive.
The added public import makes the definition already used by the signature
available to importers; it does not change its mathematical meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso | M2 | Restored; explicit public import fixes the reproduced compiler error. |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso | quarantined | Its existing application of the unchanged theorem needs no adaptation. |

No live Lean module imports the quarantined item. The archived direct consumer
is listed above and is preserved. Its own other quarantined dependencies remain
separate rework items. No consumer signature or proof changes are forced.

## Status

landed 20261020T145525-L-2406835 2026-10-20 (merge of deliver/M2/Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso)

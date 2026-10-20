# Retire Sheaf.Algebra.Homology.KFlatPullback

## Reason

The human's retirement instruction in `retire-sheaf-twins-20261020.md` requires
using the official upstream twin and withdrawing the duplicate. The old module has
zero proof holes. The twin constructs the same ring map and pullback complex and
states preservation using `IsKFlatTensor`, definitionally equal to the earlier
`IsAcyclicTensorKFlat`. No retained consumer signature or proof body changes are required. Preflight also
requires wrapping six pre-existing overlong instance declarations in global
monoidal normalization; only whitespace changes on those lines.

## Old

```lean
import Sheaf.Algebra.Homology.KFlatPullback
```

The global monoidal normalization consumer used the public form of this import.
The DAG attachment pointed to the Sheaf module and recorded the old predicate name.

## New

```lean
import WeilConjectures.Algebra.Homology.KFlatPullback
```

The public import in global monoidal normalization remains public. The node
`lem-pc-kflat-pullback-preservation` points to the upstream module and declaration,
with the upstream signature using `IsKFlatTensor`. The duplicate is withdrawn using
`deleted.txt`. Upstream files and target statements are untouched; no proof is
replaced by `sorry`, and no definition is hollowed.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | unclaimed | Withdraw unused duplicate; its DAG attachment points at the official twin. |
| `Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.DerivedHomPushforwardKFlatModel` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.FlatModelFiniteFreeComparison` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound` | unclaimed | Replace only the KFlatPullback import by its twin. |
| `Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization` | unclaimed | Replace the public import; wrap six pre-existing overlong instance declarations for preflight. |

The hand-off listed 36 consumers; the other 26 files have already been retired
and are absent from the current source tree. Searching all remaining Lean sources
finds exactly the ten direct consumers above and no upstream consumer of the copy.

The consumer `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` has no
importers in either library root and is itself a listed retirement item, with no
current holder. Retire this unused duplicate too, as authorized by the hand-off's
pruning of dead copies. Its six public results are retained in the official twin;
`lem-pc-affine-derived-pullback-tensor-tilde` points there. It compiled in the first
consumer batch (49.5 seconds). Subsequent validation hit the 60-second limit;
diagnostic-only attempts to reduce elaboration were discarded. No module is split,
no proof is replaced by a hole, and no retained signature changes. Neither the
source library nor the project targets are edited.

A source import-closure scan finds no newly coexisting Sheaf/upstream twin pairs
in any retained consumer environment.

The return of head `b44ac794a90` followed an intervening landing
`ba90540c48d` in the item file. Re-read the current item: its intervening
changes use the official tensor-pullback stalk-complex API and its canonical
ring map. The replacement KFlatPullback twin already uses that API. Retiring the
current item therefore keeps that repair through the official implementation.
All nine consumer files were reconstructed from current sources and the reviewed
import changes reapplied. This preserves the concurrent official IsKFlatTilde
import in AffineKFlatPullbackChartComparison. Both node copies change only their
Lean attachments. The delivery is rebuilt against current sheaf-dag.

## Status

landed 20261020T153016-L-2863412 2026-10-20 (merge of deliver/P5/Sheaf.Algebra.Homology.KFlatPullback)

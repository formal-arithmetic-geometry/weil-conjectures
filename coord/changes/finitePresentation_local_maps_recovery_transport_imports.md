# AlgebraicGeometry.finitePresentation_local_maps_recovery_transport

## Reason

The proof uses local irreducibility of ordinary pullback to prevent expensive unfolding
of chart objects during categorical rewriting. It also removes a redundant direct
public import of OpenCoverTensorPullbackComparison. That module is still publicly
reexported through both LocalMapRecovery and LocalMapPullbackFamily, which remain
public imports. The declaration signature, definitions, and effective public exports
are unchanged. This record documents import and local proof-command changes flagged
by the delivery interface checker; no target meaning is affected.

## Old

```lean
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import Sheaf.AlgebraicGeometry.LocalMapPullbackFamily
public import Sheaf.AlgebraicGeometry.LocalMapRecovery

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison
```

## New

```lean
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Sheaf.AlgebraicGeometry.LocalMapPullbackFamily
public import Sheaf.AlgebraicGeometry.LocalMapRecovery
import Sheaf.AlgebraicGeometry.LocalMapRecoveryComposition
import Sheaf.AlgebraicGeometry.TensorPullbackCompositionAssociativity

attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison
```

The theorem signature is byte for byte unchanged. The theorem-local transparency
options are false while proving the new reduction, and unusedVariables suppression
is confined to that declaration (its original signature includes the unused let V).
These options and local attributes affect elaboration of this proof only.

## Users

`tools/downstream.py --uses AlgebraicGeometry.finitePresentation_local_maps_recovery_transport`
finds the following two textual users. Neither requires adaptation: the theorem's
statement is unchanged and every previously exported dependency remains public.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapRecoveryTransport | F2 | Same signature; new proof. |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility | unclaimed in local snapshot | No signature or effective export change; no adaptation. |

## Status

landed 20261013T211059-L-390407 2026-10-13 (merge of deliver/F2/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapRecoveryTransport)

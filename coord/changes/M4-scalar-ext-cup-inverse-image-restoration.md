# scalarExtCup_inverseImage proof import restoration

## Reason

The current rework entry quarantines the item because its first-factor import
loads upstream field-linear operation definitions into an environment already
containing the local copies. This produces the recorded duplicate declaration
error for `AlgebraicGeometry.Scheme.Modules.externalCupCoefficients`.
Restore the archived theorem with its public signature unchanged and prove
first-factor coherence privately in its existing local operation environment.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ScalarExtCupInverseImageFirst
import Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond
```

The main proof rewrites by `scalarExtCup_inverseImage_first`.

## New

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison
import Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond
```

Three proved private helpers adapt the first-factor coherence proof from the
upstream theorem, specializing the recorded generic Ext identity comparison.
The main proof rewrites by private `firstTransport`. No public declaration,
mathematical signature, definition, instance or upstream file is changed.

## Users

The normal downstream tool reports the item as unknown because it is currently
quarantined. Source searches in both `lean/` and `quarantine/` find the direct
consumer below. The transitive consumer listed in the same rework cluster is
also retained. Existing consumers need no adaptation because the public import
and the complete public theorem signature remain verbatim those of the archive.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage | M4 | Restore compilation with private coherence proofs. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | quarantined, separate rework | Direct consumer; signature and public environment unchanged. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | quarantined, separate rework | Transitive consumer; no adaptation required. |

No other module is adapted. No target statement or target-used definition changes.

## Status

landed 20261020T145527-L-2407280 2026-10-20 (merge of deliver/M4/Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage)

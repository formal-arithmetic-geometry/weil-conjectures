# Scalar normalization foundation imports

## Reason

The ordinary balancing-chain module publicly imported the final scalar-mate theorem,
whose proof imports ProEtaleScalarTensorNormalization. This made the planned use of
balancing-chain in this item cyclic. The proved UnboundedCoefficientPullbackModel had
the same unused theorem import. Both files use only the identification declarations
from that module; those declarations already have their own identification-only file.
Replacing the imports makes the existing ordinary balancing and ordinary-mate proofs
available to the normalization argument without circularity.

## Old

In each of Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain and
Sheaf.Paper.UnboundedCoefficientPullbackModel:

```lean
public import Sheaf.Paper.ProEtaleScalarMateNormalization
```

## New

In each of those two modules:

```lean
public import Sheaf.Paper.ProEtaleScalarMateIdentifications
```

All declarations, signatures, attributes and proof bodies in both modules are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain | unclaimed | Foundation import corrected; all declarations and the existing balancing hole remain verbatim. |
| Sheaf.Paper.UnboundedCoefficientPullbackModel | unclaimed | Sole existing direct importer of balancing-chain. It explicitly imported the scalar-mate module too; its unused import is corrected in the same packet. No declaration uses the removed final theorem. Compiled against the corrected balancing module. |

There are no existing live direct importers of UnboundedCoefficientPullbackModel.
New modules of this delivery import the corrected foundations. The main item and
both new compatibility modules are checked together in import order. The target
statements and all definitions appearing in their statements retain their meanings.

## Status

landed 20261027T103432-L-1077270 2026-10-27 (merge of deliver/H7/Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization)

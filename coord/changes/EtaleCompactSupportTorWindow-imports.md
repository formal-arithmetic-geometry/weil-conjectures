# Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow imports

## Reason

The theorem proof no longer uses the three public imports below. It uses the source
flat-extension theorem and generic bounded-flat criteria through private imports, so these
imports need not be exposed to importers of the module. Removing them is a proof-only
pruning change; the theorem signature is unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
```

## New

Those three public imports are removed. The remaining public imports and all private proof
imports are unchanged from the delivered module.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow | R3 | The item itself compiles with the reduced public interface. |

No other module currently imports this item directly.

## Status

landed 20261023T151948-L-427689 2026-10-23 (merge of deliver/R3/Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow)

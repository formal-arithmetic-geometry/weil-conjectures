# Sheaf.AlgebraicGeometry.EtaleSingleTensoratorPullback public imports

## Reason

The item statement and proof do not need `Derived.TensorStructure`. Retain only
`Derived.Invertible` publicly and import the proved support modules privately.
No declaration signature, instance, attribute, or definition changes.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
```

## New

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import Sheaf.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import Sheaf.AlgebraicGeometry.EtaleSinglePullbackCounit
import Sheaf.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility | unclaimed | Already explicitly imports `Derived.TensorStructure`; compiled unchanged against this delivery. |

No direct importer needs adaptation. The target statements and their definitions
remain identical.

## Status

landed 20261026T235923-L-1469189 2026-10-26 (merge of deliver/N1/Sheaf.AlgebraicGeometry.EtaleSingleTensoratorPullback)

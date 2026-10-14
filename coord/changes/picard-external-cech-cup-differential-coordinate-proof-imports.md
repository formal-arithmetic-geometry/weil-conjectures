# PicardExternalCechCupDifferentialCoordinate proof imports

## Reason

The differential-coordinate proof now uses the promoted pure-tensor Leibniz theorem. The
three old plain proof imports were redundant because the public bidegree module already
provides the declarations used by this file. The new Leibniz import is proof-only.

## Old

```lean
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.Paper.CechCupProduct
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz
```

The public declarations and signatures of the coordinate module are unchanged. The removed
imports were private to its implementation, and the added import is private to the proof.

## Users

| module | group holding it | effect |
|---|---|---|
| (none) | unclaimed | The interface checker reports no named declaration change; downstream modules continue to use the unchanged coordinate declarations. |

## Status

landed 20261014T152111-L-1084380 2026-10-14 (merge of deliver/N4/Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate)

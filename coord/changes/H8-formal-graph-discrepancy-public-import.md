# AlgebraicGeometry.formalGraph_discrepancy_zero

## Reason

The current rework archive uses `Scheme`, coherent modules, and completion in its
public theorem signature while importing their defining module only privately.
The recorded global build fails with unknown identifier `Scheme`. Restore the
archived source with its statement dependency publicly visible. No definition or
theorem signature changes, and no target statement needs renewed semantic review.

## Old

```lean
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero | H8 | Restored from quarantine; statement imports fixed; all proof text preserved. |
| Sheaf.AlgebraicGeometry.FormalGraphFirstQuotientEpi | Not adapted; quarantined | Its existing discrepancy theorem call keeps exactly the same type; no consumer edit required. |

The upstream `WeilConjectures.AlgebraicGeometry.FormalGraphFirstQuotientEpi`
contains its own proof and does not import this module. No other active Lean
module imports this quarantined module. The existing parent DAG dependency is
preserved.

## Status

landed 20261020T145517-L-2405177 2026-10-20 (merge of deliver/H8/Sheaf.AlgebraicGeometry.FormalGraphDiscrepancyZero)

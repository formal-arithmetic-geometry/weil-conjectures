# AlgebraicGeometry.smooth_connected_fibre_normal_integrality

## Reason

Prove the theorem with the retained generic geometry core over `Spec K`. Prune unused
imports: the statement needs `Fiber`, not the larger base-change-conventions module,
and neither its statement nor proof uses geometric integrality or properness.
The theorem's signature, visibility and mathematical meaning are unchanged.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Proper
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
```

The other imports are retained. `AffineScheme` is a private proof import for
`Scheme.isIntegrallyClosed_stalk_Spec`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothConnectedFibreNormalIntegrality | W2 | Its theorem now has a complete proof. |

The shared source tree has zero direct Lean importers of this module (checked with
an anchored import search). No consumer requires adaptation. The DAG parents still
use this unchanged theorem, so none is withdrawn. No target statement or definition
is changed.

## Status

landed 20261026T092954-L-3484590 2026-10-26 (merge of deliver/W2/Sheaf.AlgebraicGeometry.SmoothConnectedFibreNormalIntegrality)

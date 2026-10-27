# AlgebraicGeometry.geometric_fibre_affine_chart_test imports

## Reason

The theorem's statement and complete proof use only Mathlib's fibre, pullback,
residue-field, tensor-spectrum, open-cover and reducedness APIs. The public import
of `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` provides none of the
names needed here. Removing it avoids bringing unrelated source-library dependencies
into this item's import closure. No declaration signature or definition changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.TensorProduct.Maps
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.GeometricFibreAffineChartTest`
reports zero downstream modules. A direct-import search also finds no importers.
The DAG parents remain valid: the theorem's statement is unchanged, and they may
import the explicit modules they need when their proofs are written.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeometricFibreAffineChartTest | R6 | Complete proof and unused imports removed; unchanged declaration type. |

No direct importer requires adaptation or compilation. No target statement or
underlying definition changes, so no target's statement review is reopened.

## Status

landed 20261026T092459-L-3435309 2026-10-26 (merge of deliver/R6/Sheaf.AlgebraicGeometry.GeometricFibreAffineChartTest)

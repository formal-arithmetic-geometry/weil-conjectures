# AlgebraicGeometry.Scheme.singletonProduct_affine_ring import interface

## Reason

The ring calculation uses no tensor-section comparison definitions. Replace the large
public normalization-module import with the Mathlib prerequisites of its unchanged
statement, and keep the extra proof imports private. This prunes an irrelevant dependency
without changing any theorem or definition. New `variable` commands are contained within
`section TensorColimit ... end TensorColimit`; all new declarations are private.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
```

The public theorem's signature remains verbatim from the original file; only its proof
changes. Its existing namespace, universe, opens, scoped notation, and visibility remain.

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.RingTheory.PiTensorProduct
```

The public imports supply the étale category and indexed tensor algebra in the
statement. The étale module already exposes the product-existence instances needed by
the statement; a statement-only scratch compilation verified this without importing
Over.Products directly. The three plain imports supply only proof lemmas and
constructions, including the over-product/wide-pullback cone equivalence. No target statement or definition used by a target is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonProductRing | C1 | Original theorem signature and visibility preserved; import interface simplified; proof completed. |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel | unclaimed in the local snapshot | Direct importer. |
| Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan | unclaimed in the local snapshot | Direct importer. It independently publicly imports the normalization module; its signature and available declarations are unchanged. No edit required. |

The source import search finds exactly these two direct importers. Both independently
publicly import the normalization module. Both compile against the delivered module
without adaptation; no forced-adaptation exception is used.

## Status

landed 20261013T121220-L-3505569 2026-10-13 (merge of deliver/C1/Sheaf.AlgebraicGeometry.EtaleAffineSingletonProductRing)

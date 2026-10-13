# exists_tensorHom_linearEquiv proof context

## Reason

The static interface check flags the section variables and local notation used by the new
private proof helpers, and removal of three redundant public imports. There is no change
to an existing declaration's signature, definition, or visibility. All instance declarations
added for helper elaboration are local to the helper section. The proof-only source import
provides naturality of the tensor comparison. Each removed public import remains transitively
public through `TensorProduct` and `HomModule`, so importers retain its declarations.

## Old

```lean
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
```

No helper section or helper-local instances.

## New

The above three direct imports are removed as redundant. Their modules are still public
through `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` (which publicly imports
source `Sheaf.Monoidal`, which publicly imports all three). Added:

```lean
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
```

A `section Helpers` contains private proved helpers, local notation, section variables,
and local instances equal to existing `monoidalCategory R` and `homModule R.obj ...`.
The section ends before the original theorem. Its original statement is verbatim unchanged.
No target meaning or downstream statement changes. No forced adaptations are needed.

## Users

Direct importers (the changed theorem itself has no external textual uses):

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | {"who": "N2", "t": 1791855407.540847, "since": "2026-10-13T01:36:47Z"} | No adaptation: removed imports remain public transitively; theorem unchanged. |
| `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen` | {"who": "F4", "t": 1791854798.4701376, "since": "2026-10-13T01:26:38Z"} | No adaptation: removed imports remain public transitively; theorem unchanged. |
| `Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology` | unclaimed | No adaptation: removed imports remain public transitively; theorem unchanged. |
| `Sheaf.AlgebraicGeometry.LocallyFreeExtSecondNaturality` | unclaimed | No adaptation: removed imports remain public transitively; theorem unchanged. |

All transitive importers also retain the same public declarations, because the three removed
imports are still in the public transitive closure. No module is adapted in this delivery.

## Status

landed 20261013T031540-L-3570916 2026-10-13 (merge of deliver/G4/Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction)

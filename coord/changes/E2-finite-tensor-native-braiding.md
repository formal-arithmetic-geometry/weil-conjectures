# WeilConjectures.PurityFiniteSetting.finiteTensorStructuralCoherence

## Reason

Restore the quarantined module assigned in `coord/rework.tsv`, following the
2026-10-23 upstream sync. Its symmetry-square statement cannot elaborate because
the native derived braiding is now exposed as a definition rather than a global
instance. Importing `DerivedCategory.Monoidal.Braided` alone does not register it.
The archived source fails at its `FiniteTensorSymmetrySquare` application with
`failed to synthesize instance ... BraidedCategory (DerivedCategory (Sheaf ...))`.

## Old

The archived header proceeds directly from the scoped tensor notation to the
namespace:

```lean
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting
```

## New

```lean
open scoped TensorProduct
-- The native derived braiding is a definition, not a global instance.
attribute [local instance] _root_.DerivedCategory.braidedCategory'

namespace WeilConjectures.PurityFiniteSetting
```

This supplies the published native Koszul braiding to the symmetry square for
both coefficient categories. It adds no declaration or global instance. All
archived declaration text, imports, definitions and proof bodies are preserved.
In particular this does not use the separate, still-unproved symmetric structure.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteTensorPresentationReduction` | E2 | Restored from quarantine; local elaboration repair. |

`tools/downstream.py Sheaf.Paper.FiniteTensorPresentationReduction --uses
finiteTensorStructuralCoherence` reports the module as unknown because it is
quarantined. A source search in both `lean/` and `quarantine/` finds no importing
module and no external use of its declarations. DAG parents and the existing
Lean attachment are preserved: this is restoration, not withdrawal or pruning.
No consumer needs adaptation, and no target or mathematical statement changes.

## Status

landed 20261024T014522-L-2210482 2026-10-24 (merge of deliver/E2/Sheaf.Paper.FiniteTensorPresentationReduction)

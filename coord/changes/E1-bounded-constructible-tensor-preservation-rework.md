# boundedConstructible_tensor_unit / boundedConstructible_tensor_closure

## Reason

Restore the assigned module from the archive named by `coord/rework.tsv` after
upstream synchronization `5f7b33eac`. The archived module has zero holes. Its unit
proof calls the private helpers `AlgebraicGeometry.ProEtale.constructible_of_iso`
and `AlgebraicGeometry.ProEtale.constructible_of_isZero`. Those helpers were moved
from the upstream derived-category module to its extracted `Sheaf.UpstreamExtra`
module. Importing all of the old upstream module no longer makes them available.

## Old

```lean
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.ConstructibleSheaf.OpenClosed
```

## New

```lean
import all Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
```

The private import follows the existing helpers to their new home. The unused
ordinary `OpenClosed` import is removed. All archived public imports, theorem
signatures, universes, visibility, attributes and proof bodies are preserved.
Neither a definition nor a target statement changes. Both DAG nodes retain their
existing Lean attachments and the same proof route and dependencies.

## Users

`tools/downstream.py` reports the item as unknown because it is quarantined.
Searching both `lean/` and `quarantine/` finds the two direct consumers below.
They use the unchanged public unit and closure theorems. No adaptation is needed.
No other group's module is edited. A separate consumer importing only the restored
module applies each theorem at its full archived signature, checked through
`lcompile.py` together with the restored module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation | E1 | Restore and repair its private proof import. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed, quarantined | Same public signatures and imports; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed, quarantined | Same public tensor-closure signature; no adaptation. |

## Status

landed 20261020T160751-L-3404655 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation)

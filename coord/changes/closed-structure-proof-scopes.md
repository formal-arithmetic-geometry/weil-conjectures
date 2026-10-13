# AlgebraicGeometry.Scheme.Modules.closed_structure_ideal_product_iso

## Reason
The proof needs tensor notation, image notation, and private comparison helpers.
The returned version duplicated five existing private helper statements. This repair
removes `ideal_qc` and generalizes the image, tensor-range, morphism-equality and
subobject-order helpers; it cannot import the duplicates because of import cycles.
The conservative interface scanner flags the added lexical namespace and open commands.
No existing declaration signature, definition, instance, attribute or public import changes.

## Old
```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
```

The original theorem signature and docstring are unchanged byte for byte.

## New
```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme
```

Four proved private helpers with generalized statements occur in that namespace,
followed by these exact commands:

```lean
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
```

The original theorem stays under its original namespace. The declaration-local
transparency option facilitates proof elaboration.
These lexical commands do not export notation or alter downstream declarations.

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LocalClosedIdealMapExtension | unclaimed | Existing signature and meaning identical; no adaptation required. |

No downstream module mentions a changed declaration: the scanner reports only lexical
commands. All original public imports and the original theorem signature are preserved.

## Status
landed 20261013T082333-L-1631713 2026-10-13 (merge of deliver/C2/Sheaf.AlgebraicGeometry.ClosedStructureIdealProductIso)

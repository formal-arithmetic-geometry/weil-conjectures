# CategoryTheory.ordinaryTriangleCounitCone

## Reason

The assigned file predates Lean's module-system conversion. The current brief requires
every delivered file to use `module`, public imports for its statement, and an exposed
public section. Convert this header while proving the existing theorem. This changes
the file-level visibility commands, which preflight requires documenting even though
the theorem's signature and its two statement imports are preserved.

## Old

```lean
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Adjunction.Basic
```

The file had no `module` command or `@[expose] public section`.

## New

```lean
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.Triangulated.Recollement
```

Add `@[expose] public section` after the module docstring. The recollement import is
proof-only. The public theorem retains its original signature verbatim, including all
six universe parameters and every category, shift, triangulation and adjunction
hypothesis. Its proof is completed; there are no new declarations or definitions.

## Users

`tools/downstream.py Sheaf.CategoryTheory.OrdinaryTriangleCounitCone --uses
CategoryTheory.ordinaryTriangleCounitCone` checks the downstream source modules.
A source search finds no external importer or use of this declaration in either
`lean/Sheaf` or `lean/WeilConjectures`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.OrdinaryTriangleCounitCone | W7 | Convert the header and prove the existing theorem; its signature stays identical. |

No consumer needs adaptation. No target statement or definition changes.

## Status

landed 20261019T112610-L-3960675 2026-10-19 (merge of deliver/W7/Sheaf.CategoryTheory.OrdinaryTriangleCounitCone)

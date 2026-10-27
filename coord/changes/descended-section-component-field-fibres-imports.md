# AlgebraicGeometry.descended_section_component_field_fibres

## Reason

The statement needs the scheme fibre API and geometric connectedness, rather than
the broad project base-change conventions or geometric integrality. Narrow its
public imports while completing its proof. No declaration, definition, instance,
or theorem signature changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DescendedSectionComponentFieldFibres | Y7 | Proof completed with narrower statement imports. |

A repository-wide search found no current direct Lean importers or other references
to `AlgebraicGeometry.descended_section_component_field_fibres`. Its DAG parents
remain supported: the theorem retains exactly its existing signature, and the
fibre/component constructions and all four steps of the node's proof remain used.
There are no direct importers to adapt or compile. No target uses a changed
definition, since no definition changes.

## Status

landed 20261026T093106-L-3522271 2026-10-26 (merge of deliver/Y7/Sheaf.AlgebraicGeometry.DescendedSectionComponentFieldFibres)

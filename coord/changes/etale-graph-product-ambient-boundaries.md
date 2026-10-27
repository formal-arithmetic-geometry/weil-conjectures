# AlgebraicGeometry.Etale.etaleGraphProductAmbientPasting

## Reason

Extract the already proved ambient geometry so the source-lift and target-square
subgrid lemmas can import it without importing their own consumer. This is a
proof dependency boundary, not a workaround for the compile time limit. Every
existing public declaration keeps its name, signature, attributes and body;
the original module publicly reexports the geometry module. No source-library
module changes. New explicit words sourceTransport and middleTail supply the
common boundary of the two strictly smaller subgrids.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphProductInterchange
```

The existing ambient geometry and lambda/interchange definitions lived in
`Sheaf.AlgebraicGeometry.EtaleGraphProductAmbientPasting` before its theorem.
Their declarations are recorded verbatim in the original item node.

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import Sheaf.AlgebraicGeometry.EtaleGraphAmbientSourcePasting
import Sheaf.AlgebraicGeometry.EtaleGraphAmbientSquarePasting
```

The geometry module retains the old public import and all those declarations
verbatim. It additionally constructs rawSquare and, for each selected side,
e_side_square, R_q, sourceTransport and middleTail. The original theorem's
signature and documentation are unchanged. All original public imports remain
transitively visible.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleGraphProductAmbientPasting` | C3 | Item: preserves its theorem signature and publicly reexports all moved declarations. |
| `Sheaf.AlgebraicGeometry.EtaleGraphProductRowPasting` | unclaimed | Uses preserved declarations through the original public reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGraphProductShrinkPasting` | unclaimed | Uses preserved declarations through the original public reexport; no adaptation. |

`tools/downstream.py --direct` lists only EtaleGraphProductShrinkPasting.
Its public import preserves all transitive visibility. The full transitive
import closure has 4950 modules; none loses any public declaration or import.
The table lists all textual consumers of the moved namespaces and theorem.

## Status

landed 20261026T065319-L-2810813 2026-10-26 (merge of deliver/C3/Sheaf.AlgebraicGeometry.EtaleGraphProductAmbientPasting)

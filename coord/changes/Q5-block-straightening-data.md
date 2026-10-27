# AlgebraicGeometry.HilbertCoefficient.BlockStraighteningInput and related block interfaces

## Reason

The initial-jet, geometric-chart, and conjugacy steps must import the block definitions
without importing the theorem that combines them. Move the existing concrete definitions
and structures verbatim into a new public data module. The item publicly reexports it.
Add the projection-free `BlockStraighteningGeometry` structure to state the geometric
construction independently of all operator transport. No existing definition body or
signature changes; the theorem statement is unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
public import Sheaf.RingTheory.FormalInitialDiagram
public import Sheaf.RingTheory.FiniteCoefficientExpression
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
```

The declarations `blockVariableEquiv` through `BlockStraighteningOutput` were defined
in `Sheaf.AlgebraicGeometry.BlockStraighteningProjectionTransport`.

## New

```lean
public import Sheaf.AlgebraicGeometry.BlockStraighteningData
```

`BlockStraighteningData` has exactly the four original public imports. All existing
block definitions and structures are moved there unchanged, with the same namespaces,
visibility, universes, binders, and bodies. The new `BlockStraighteningGeometry` contains
the geometric fields of `BlockStraighteningOutput` and a residue-map surjectivity field;
it contains no projection field. `BlockStraighteningOutput` itself remains verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BlockStraighteningProjectionTransport | Q5 | Publicly reexports data; theorem uses the separate initial-jet, chart, and conjugacy steps. |

A search for direct Lean importers of the item found none in either library root.
The DAG parent `lem-trf-regular-hilbert-coefficient-data` retains its attachment and
its dependency on the item unchanged. No target or source-library declaration changes.

## Status

landed 20261026T092330-L-3424116 2026-10-26 (merge of deliver/Q5/Sheaf.AlgebraicGeometry.BlockStraighteningProjectionTransport)

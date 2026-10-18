# Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne import interface

## Reason

The proof uses the existing relative-dimension comparison and base-change instance,
so the original fibre-dimension proof imports are unnecessary. The canonical curve
module supplies the topological dimension field directly. Removing the retired
base-change re-export and the redundant topological-dimension public import does
not change any declaration signature, definition, visibility, or mathematical meaning.
No target definition changes and no target statement review is reopened.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
--uses curve_baseChange_smoothOfRelativeDimension_one` lists exactly the two modules
below. There is only one direct importer, `HilbertToPicardMorphism`, through a
proof-only import. It already imports both base-change convention modules independently
and publicly imports `Curve.SmoothProjective`, which transitively publicly imports
`WeilConjectures.Mathlib.Topology.KrullDimension`. Thus no user loses required APIs.
The theorem has no textual consumers yet: its parent's proof is still a placeholder.
Both original consumers were compiled successfully against the sandbox overlay.
Neither consumer is edited; their declarations and statements remain identical.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not queried (not edited) | No adaptation; independent imports supply the removed re-exports. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not queried (not edited) | No adaptation; imports HilbertToPicardMorphism publicly and has its own base-change conventions imports. |

## Status

landed 20261018T062720-L-638946 2026-10-18 (merge of deliver/D2/Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne)

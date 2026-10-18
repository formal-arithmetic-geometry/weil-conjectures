# AlgebraicGeometry.flat_composite_fibre_dimension_at_point

## Reason

The assigned source is a legacy non-module file. The worker brief requires every
delivered file to use the Lean module system and proof dependencies to be ordinary
imports. Convert this file to `module`, retain statement dependencies as public
imports, and expose its existing theorem publicly. This necessarily changes the
legacy file's transitive import visibility. No theorem signature or mathematical
definition changes. The only removed mathematical dependency is the separate
finite-type dimension-finiteness bound, which the additive proof does not need.

## Old

```lean
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.CompositeFibreLocalModels
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
```

The theorem signature was:

```lean
theorem flat_composite_fibre_dimension_at_point
    {U X S : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ S) (u : U)
    [LocallyOfFiniteType a] [LocallyOfFiniteType f]
    (hflat : (a.stalkMap u).hom.Flat) :
    topologicalKrullDimAt ((a ≫ f).asFiber u) =
      topologicalKrullDimAt (a.asFiber u) + topologicalKrullDimAt (f.asFiber (a u))
```

## New

```lean
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.CompositeFibreLocalModels
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.PointCount
```

The module docstring is followed by `@[expose] public section`.
The existing theorem has exactly the old signature and a complete proof.
Four proved private helpers are implementation details of that proof.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
--uses flat_composite_fibre_dimension_at_point` reported zero downstream modules
and one textual use, the theorem's own module (2026-10-18).

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint | Q3 | Convert legacy interface; prove the unchanged theorem. |

There are no downstream statements to adapt. No target statement uses a changed
definition, because no definition is changed.

## Status

landed 20261018T062853-L-670453 2026-10-18 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint)

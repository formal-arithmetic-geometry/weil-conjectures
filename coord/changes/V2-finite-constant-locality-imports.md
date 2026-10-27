# AlgebraicGeometry.ProEtale.finiteConstantStratified_zariski_locality

## Reason

Remove four unused public imports from the assigned module. The constructibility
definition module already provides all types appearing in the unchanged theorem
signature, including the topological quasi-separatedness predicate.

## Old

```lean
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
```

## New

```lean
public import Sheaf.Paper.CondensedConstantConstructibility
```

## Users

`tools/downstream.py Sheaf.Paper.FiniteConstantStratifiedZariskiLocality --uses
AlgebraicGeometry.ProEtale.finiteConstantStratified_zariski_locality` reports zero
downstream modules and only the declaration's own module as a name user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteConstantStratifiedZariskiLocality | V2 | Unchanged theorem signature; unused imported interfaces removed. |

No target statement uses the changed public import surface. No definition changes.

## Status

landed 20261023T170220-L-2076650 2026-10-23 (merge of deliver/V2/Sheaf.Paper.FiniteConstantStratifiedZariskiLocality)
